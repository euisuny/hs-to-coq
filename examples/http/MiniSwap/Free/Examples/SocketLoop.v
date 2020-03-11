Typeclasses eauto := 5.

From QuickChick Require Import QuickChick.

Set Implicit Arguments.
Set Contextual Implicit.
Generalizable All Variables.

Require Import List.
Import ListNotations.

Require Import Nat.

From Custom Require Import
     String
     List.

Require Import DeepWeb.Free.Monad.Free.
Require Import DeepWeb.Free.Monad.Trace.
Require Import DeepWeb.Free.Monad.Spec.
Require Import DeepWeb.Free.Monad.Common.
Import SumNotations.
Open Scope sum_scope.

Typeclasses eauto := 10. (* Instance search depth limit. *)

Module Socket.
Section SocketSection.

(* TODO: use QuickChick's mutation testing framework? *)
Inductive variant := Fine | DropSend | TwoSend.

Variable bug : variant.

Variable socket : Type.
Variable message : Type.
Definition sock_addr : Type := unit.

Variable socket_eqb : socket -> socket -> bool.

Inductive socketE : Type -> Type :=
| Socket : socketE socket
| Bind : socket -> sock_addr -> socketE unit
| Listen : socket -> socketE unit
| Select :
    list socket (* Read *) ->
    list socket (* Write *) ->
    list socket (* Exception *) ->
    socketE (list socket * list socket * list socket)
| Accept : socket -> socketE socket
| Recv : socket -> socketE message
| Send : socket -> message -> socketE unit
| Close : socket -> socketE unit.

Inductive conn_state :=
| RECVING | SENDING (msg : message) | DONE | DELETED.

Record connection := Connection {
    fd : socket;
    st : conn_state;
  }.

Definition accept_sock (sock : socket) (conns : list connection)
  : itree socketE (list connection) :=
  fd <- liftE (Accept sock);;
  let conn := {| fd := fd; st := RECVING |} in
  ret (conn :: conns).

Definition conn_read (conn : connection) : itree socketE connection :=
  match st conn with
  | RECVING =>
    msg <- liftE (Recv (fd conn));;
    let st :=
        match bug with
        | DropSend => DONE
        | _ => SENDING msg
        end in
    ret {| fd := fd conn; st := st |}
  | _ => ret conn
  end.

Definition conn_write (conn : connection) : itree socketE connection :=
  match st conn with
  | SENDING msg =>
      let send_ := liftE (Send (fd conn) msg) in
      match bug with
      | TwoSend => send_;; send_
      | _ => send_
      end;;
      ret {| fd := fd conn; st := DONE |}
  | _ => ret conn
  end.

Definition process (conn : connection)
          (read_ready : bool)
          (write_ready : bool)
  : itree socketE connection :=
  if read_ready then
    conn_read conn
  else if write_ready then
    conn_write conn
  else
    ret conn.

Definition clean_connections (conns : list connection)
  : itree socketE (list connection) :=
  forM conns
      (fun conn =>
         match st conn with
         | DONE =>
           liftE (Close (fd conn)) ;;
           ret {| fd := fd conn; st := DELETED |}
         | _ => ret conn
         end).

Notation "sock \in socks" :=
  (existsb (fun s => socket_eqb s sock) socks)
    (at level 70, no associativity).

Definition is_recving cs :=
  match cs with
  | RECVING => true
  | _ => false
  end.

Definition is_sending cs :=
  match cs with
  | SENDING _ => true
  | _ => false
  end.

Definition recv_socks conns :=
  map fd (filter (fun conn => is_recving (st conn)) conns).

Definition send_socks conns :=
  map fd (filter (fun conn => is_sending (st conn)) conns).

CoFixpoint select_loop'
           (conns : list connection)
           (sock : socket)
  : itree socketE void :=
  let rs := recv_socks conns in
  let ws := send_socks conns in
  rwe_ready <- liftE (Select (sock :: rs) ws []);;
  let '(rs_ready, ws_ready, _) := rwe_ready in
  if (null rs_ready && null ws_ready)%bool then
      select_loop' conns sock
  else
    conns' <- (if sock \in rs_ready then
                accept_sock sock conns
              else
                ret conns);;
    let process' conn :=
        process conn
                (fd conn \in rs_ready)
                (fd conn \in ws_ready) in
    conns'' <- forM conns' process';;
    conns''' <- clean_connections conns'';;
    select_loop' conns''' sock.

Definition select_loop : socket -> itree socketE void :=
  select_loop' [].

Definition placeholder_addr : sock_addr := tt.

Definition main : itree socketE void :=
  fd <- liftE Socket;;
  liftE (Bind fd placeholder_addr);;
  liftE (Listen fd);;
  select_loop fd.

End SocketSection.
End Socket.

Module HighLevelSpec.
Section HighLevelSpecSection.

(* A high-level specification of a server that receives messages
   and sends them back, only in terms of externally observable
   "network events": [accept], [recv], [send].

   Compared to the above, this high-level specification abstracts
   from irrelevant low-level concerns/implementation details
   such as:
   - using [select] to find connections that are ready;
     the specification just picks a connection
     nondeterministically;
   - ordering: [main] above first tries to accept a
     connection and then goes through all ready connections
     in one iteration; but here, we only care that the server
     does either of three things, in any order:
     + accept a new connection;
     + receive a message from such a connection and store it;
     + send back the received message;
   - resource management/error handling:
     at this level, network operations are assumed to succeed,
     and we don't model the [DONE]/[DELETED] states anymore
     (should we?).

   Extensible effects: We add failure and nondeterminism to
   the language as event constructors of separate types, and
   combine event types using [+']. The modularity makes the
   presentation nicer, but is not central to the point here.

   TODO:
   - Formalize a relation between [main] above and
   [server_process] below.
   - Can we test that relation before proving it?
 *)

(* The same as [Socket.variant] but maybe there are
   different sets of bugs to invent? *)
Inductive variant := Fine | DropSend | TwoSend.

Variable bug : variant.

Variable socket : Type.
Variable message : Type.

Context `{Show socket} `{Show message}.

Inductive networkE : Type -> Type :=
| Accept : networkE socket
| Recv : socket -> networkE message
| Send : socket -> message -> networkE unit.

Global Instance Show_networkE X : Show (networkE X) :=
  { show e :=
      (match e with
      | Accept => "Accept"
      | Recv s => "Recv " ++ show s
      | Send s m => "Send " ++ show s ++ " " ++ show m
      end)%string }.

(* The event type for this implementation. *)
Definition specE := networkE +' nondetE +' failureE.

Section NetworkCommands.

Context `{Convertible networkE E}.

Definition accept : itree E socket := liftE (convert Accept).
Definition recv (e : socket) : itree E message :=
  liftE (convert (Recv e)).
Definition send (e : socket) (m : message) : itree E unit :=
  liftE (convert (Send e m)).

End NetworkCommands.

(* Server description. *)

Inductive conn_state :=
| RECVING | SENDING (msg : message).

Record connection := Connection {
    fd : socket;
    st : conn_state;
  }.

Definition handle_pending (pending : list connection)
  : itree specE (list connection) :=
  (* Take any one element [conn] out of the pending queue.
     [pending']: remaining elements. *)
  p <- choose (select pending);;
  let '(conn, pending') := p in
  match st conn with
  | RECVING =>
    msg <- recv (fd conn);;
    match bug with
    | DropSend => ret pending'
    | _ => ret ({| fd := fd conn; st := SENDING msg |} :: pending')
    end
  | SENDING msg =>
    let send_ := send (fd conn) msg in
    match bug with
    | TwoSend => send_;; send_
    | _ => send_
    end;;
    ret pending'
  end.

Definition poll (pending : list connection)
  : itree specE (list connection) :=
  fd <- accept;;
  ret ({| fd := fd; st := RECVING |} :: pending).

CoFixpoint server_loop (pending : list connection) : itree specE void :=
  pending' <- or (handle_pending pending) (poll pending);;
  server_loop pending'.

CoFixpoint server_process : itree specE void :=
  server_loop [].

End HighLevelSpecSection.
Arguments accept {socket message E _}.
End HighLevelSpec.

Module InterpretAPI.
Module HLS := HighLevelSpec.
Section InterpretAPISection.

(* To relate the low-level [main] with the high-level
   [server_process], we can "refine" the semantics of
   [main]: we give an interpretation of [socketE]
   (the API calls) in terms of [networkE]. *)

(* Sockets as understood by the high-level spec,
   produced by [HLS.Accept]. *)
Variable hl_socket : Type.
Variable message : Type.

Definition specE :=
  HLS.specE hl_socket message.

Variable hl_socket_eqb : hl_socket -> hl_socket -> bool.

(* This interpretation instantiates the types in [Socket]. *)
Inductive socket :=
| Listening : nat -> socket
| Accepted : hl_socket -> socket.

Definition socket_eqb (s1 s2 : socket) :=
  match s1, s2 with
  | Listening n1, Listening n2 => Nat.eqb n1 n2
  | Accepted z1, Accepted z2 => hl_socket_eqb z1 z2
  | _, _ => false
  end.

Definition socketE :=
  Socket.socketE socket message.

(* We use a counter to produce new sockets via [Socket].
   (Although the above program only needs one...)
   Instead of explicitly passing the counter around,
   we just make it an event that can be handled in
   a separate pass. *)
Definition specE' := specE +' counterE nat.

Definition newSocket : itree specE' socket :=
  mapM Listening incr.

(* Nondeterministically pick a subset. *)
(* To make things simple and efficient,
   this implementation only picks 0 or 1 element. *)
Definition anySubset `{HasNondet E} X
  : list X -> itree E (list X) :=
  fix any xs :=
    match xs with
    | [] => ret []
    | x :: xs' => or (ret [x]) (any xs')
    end.

(* Here is the implementation. We just explain
   how to handle the events, and that defines a monad
   morphism via [hom].
 *)

Definition interpret X (e : socketE X)
  : itree (specE +' counterE nat) X :=
  match e with

  (* Getting a new socket. *)
  | Socket.Socket => newSocket
  | Socket.Accept _ =>
    s <- HLS.accept;;
    ret (Accepted s)

  (* [Recv] and [Send] *)
  | Socket.Recv (Accepted s) => HLS.recv s
  | Socket.Send (Accepted s) msg => HLS.send s msg

  (* We only know [Select] will return *some* subset... *)
  | Socket.Select rs ws es =>
    rs' <- anySubset rs;;
    ws' <- anySubset ws;;
    es' <- anySubset es;;
    if (null rs' && null ws' && null es')%bool then
      fail "assuming some connection is ready..."
    else
      ret (rs', ws', es')

  (* Noops/errors. *)
  | Socket.Bind (Listening _) _ => ret tt
  | Socket.Listen (Listening _) => ret tt
  (* FIXME: what happens if we do anything with a
     [Close]-d socket? *)
  | Socket.Close _ => ret tt
  (* FIXME: [Recv] and [Send] on a [Listening] socket? *)
  | Socket.Recv _
  | Socket.Send _ _ => fail "[Recv|Send] Listening"
  (* FIXME: [Bind], [Listen] on an accepted socket? *)
  | Socket.Bind _ _
  | Socket.Listen _ => fail "[Bind|Listen] Accepted"
  end.

(* Same type as [server_process]. *)
Definition main_interpreted (bug : Socket.variant) : itree specE void :=
  run_counter (hom interpret (Socket.main bug socket_eqb)).

End InterpretAPISection.
End InterpretAPI.

(* Let's try testing. *)

Module TestSpec.
Module Import HLS := HighLevelSpec.
Section TestSpecSection.

(* - Line up the implem and spec in lock-step;
     if that is not possible, fail.
   - Generate some inputs (sockets and messages).
 *)

Definition socket := nat.
Definition socket_eqb : socket -> socket -> bool :=
  Nat.eqb.

Definition message := string.
Definition message_eqb : message -> message -> bool :=
  string_eq.

Definition specE := HLS.specE socket message.

(* The following events will be left at the end:
   [testE = traceE +' arbitraryE +' nondetE +' failureE]
 *)
Definition testE := Monad.Spec.specE.
(* Unfortunate naming:
   [Monad.Spec.SpecE] is different from [HLS.specE].
   Both are meant to represent specifications of
   some sort...
 *)

Definition networkE' := HLS.networkE socket message.

(* Two computations [p q : itree specE void] can be related by
   some sort of simulation. Every effect/transition
   performed by [p] is also performed by [q]. *)
CoFixpoint simulates (p : itree specE void) (q : itree specE void)
  : itree (testE +' networkE') unit :=
  match p, q with
  | Tau p', _ => Tau (simulates p' q)
  | Vis _ ep kp, Vis _ eq kq =>
    trace ("Step: " ++ show (ep, eq));;
    match ep, eq with

    (* [p] failing means there is no transition,
       which doesn't contradict simulation. *)
    | (| Fail _ ), _ => Ret tt

    (* Every branch of the simulating computation must match
       one branch of the simulated computation:
       two interpretations of disjunction of branches,
       see [Alt] section in [Monad/Spec.v] *)
    | (| _Or_p |), _ =>
      match _Or_p in nondetE T return (T -> _) -> _ with
      | Or => fun kp => Vis Or_ (fun b => simulates (kp b) q)
      end kp

    (* [p] has a [networkE] effect, look for a match in [q]. *)
    | ( _ ||), (| Fail r ) => fail r
    | ( _ ||), (| _Or_q |) =>
      match _Or_q in nondetE T return (T -> _) -> _ with
      | Or => fun kq => Vis Alt_ (fun b => simulates p (kq b))
      end kq

    (* Match [networkE] events. *)
    | ( ep' ||), ( eq' ||) =>
      match ep' in networkE _ _ T, eq' in networkE _ _ T'
            return (T -> _) -> (T' -> _) -> _
      with
      | Accept, Accept => fun kp kq =>
        s <- accept;;
        simulates (kp s) (kq s)
      | Recv sp, Recv sq => fun kp kq =>
        if socket_eqb sp sq then
          msg <- recv sq;;
          simulates (kp msg) (kq msg)
        else
          fail "simulate: mismatched sockets"
      | Send sp mp, Send sq mq => fun kp kq =>
        if (socket_eqb sp sq && message_eqb mp mq)%bool then
          send sp mp;;
          simulates (kp tt) (kq tt)
        else
          fail "simulate: mismatched sockets or messages"
      | _, _ => fun _ _ =>
          fail "simulate: mismatched network events"
      end kp kq
    end

  | _, Tau q' => Tau (simulates p q')
  | Ret v, _ | _, Ret v => match v with end
  end.

(* Prune branches that take too long to produce
   a [networkE] effect. *)
CoFixpoint lively' X (refuel fuel : nat) (m : itree specE X)
  : itree specE X :=
  match fuel with
  | O => fail "lively: took too long to find matching event"
  | S fuel' =>
    match m with
    | Ret x => Ret x
    | Tau m' => Tau (lively' refuel fuel m')
    | Vis _ e k =>
      match e with
      | ( _ ||) =>
        Vis e (fun z => lively' refuel refuel (k z))
      | (| Or |)
      | (| Fail _ ) =>
        Vis e (fun z => lively' refuel fuel' (k z))
      end
    end
  end.

Definition lively X (refuel : nat)
  : itree specE X -> itree specE X :=
  lively' refuel refuel.

(* [networkE] handler... *)
Definition testNetworkE X (e : networkE' X)
  : itree (testE +' counterE nat) X :=
  match e with
  (* Accepted sockets should be distinct: use a counter *)
  | Accept => incr

  (* Messages are randomly generated. *)
  | Recv _ => arb

  (* Send events don't need handling ([zipSpec] checked
     that messages match between the spec and imp). *)
  | Send _ _ => ret tt
  end.

(* ... lifted to a [specE] handler. *)
Definition testSpecE X (e : (testE +' networkE') X)
  : itree (testE +' counterE nat) X :=
  match convert e with
  | (| net ) => testNetworkE net
  | ( test |) => liftE (convert test)
  end.

(* We can now turn a [specE] implementation and specification
   to a testable computation... *)
Definition testable X (m : itree (testE +' networkE') X)
  : itree testE X :=
  run_counter (hom testSpecE m).

Section TraceEquivalence.

Fixpoint match_effect X (e : networkE' X) (x : X)
         (fuel : nat) (q : itree specE void)
  : list (itree specE void) :=
  match fuel with
  | O => []
  | S fuel' =>
    match q with
    | Ret v => match v with end
    | Tau q' => match_effect e x fuel' q'
    | Vis _ eq k =>
      match eq with
      | (| Fail _ ) => []
      | (| _Or |) =>
        match _Or in nondetE T return (T -> _) -> _ with
        | Or => fun k =>
          flat_map (fun b => match_effect e x fuel' (k b))
                   [true; false]
        end k
      | ( eq' ||) =>
        match e in networkE _ _ Tp,
              eq' in networkE _ _ Tq
              return Tp -> (Tq -> _) -> _
        with
        | Accept, Accept => fun x k => [k x]
        | Recv sp, Recv sq => fun x k =>
          if socket_eqb sp sq then
            [k x]
          else
            []
        | Send sp mp, Send sq mq => fun x k =>
          if (socket_eqb sp sq && message_eqb mp mq)%bool then
            [k x]
          else
            []
        | _, _ => fun _ _ => []
        end x k
      end
    end
  end.

Variable refuel : nat.

Definition match_effect' X (e : networkE' X) (x : X)
  : list (itree specE void) -> list (itree specE void) :=
  flat_map (match_effect e x refuel).

Inductive event (E : Type -> Type) : Type :=
| Event : forall X, E X -> X -> event E.

Definition event_trace E : Type := list (event E).
Definition event_trace' E : Type := event E * list (event E).

Definition laf :=
  labeledE networkE' +' arbitraryE +' failureE.

Definition label_event X (e : specE X)
  : itree (laf +' counterE socket) X :=
  match e with
  | (| _Fail ) =>
    match _Fail with
    | Fail r => fail r
    end
  | (| _Or |) =>
    match _Or with
    | Or => arb
    end
  | ( ne ||) =>
    match ne with
    | Accept =>
      s <- incr;;
      liftE (convert (Label Accept [s]))
    | Recv s =>
      msg <- arb;;
      liftE (convert (Label (Recv s) [msg]))
    | Send s msg =>
      liftE (convert (Label (Send s msg) [tt]))
    end
  end.

Fixpoint gen_trace' (fuel : nat) (p : itree laf void)
  : G (event_trace networkE') :=
  match fuel with
  | O => returnGen []
  | S fuel' =>
    match p with
    | Tau p' => gen_trace' fuel' p'
    | Vis _ e k =>
      match e with
      | (| Fail _ ) => returnGen []
      | (| _Arb |) =>
        match _Arb in arbitraryE T return (T -> _) -> _ with
        | Arb X _ _ _ _ => fun k =>
          bindGen arbitrary
                  (fun x : X => gen_trace' fuel' (k x))
        end k
      | ( Label e (x :: _) ||) =>
        bindGen (gen_trace' fuel' (k x)) (fun es => returnGen (Event e x :: es))
      | ( _ ||) => returnGen [] (* Shouldn't happen *)
      end
    | Ret v => match v with end
    end
  end.

Definition gen_trace (fuel : nat) (p : itree specE void)
  : G (event_trace networkE') :=
  gen_trace' fuel (run_counter (hom label_event p)).

CoFixpoint match_trace (t : event_trace' networkE') (q : itree specE void)
  : PureSpec unit :=
  match q with
  | Tau q' => Tau (match_trace t q')
  | Vis _ e k =>
    match e with
    | (| _Fail ) =>
      match _Fail with
      | Fail r => fail r
      end
    | (| _Or |) =>
      match _Or in nondetE T return (T -> _) -> _ with
      | Or => fun k => Vis Alt_ (fun b => match_trace t (k b))
      end k
    | ( e' ||) =>
      let '(Event _ next x, t') := t in
      let match_trace' t' q' :=
          match t' with
          | [] => ret tt
          | ne :: t'' => Tau (match_trace (ne, t'') q')
          end in
      match next in networkE _ _ T, e' in networkE _ _ T'
            return (T' -> _) -> T -> _ with
      | Accept, Accept => fun k x => match_trace' t' (k x)
      | Recv s, Recv s' => fun k x =>
        if socket_eqb s s' then
          match_trace' t' (k x)
        else
          fail "match_trace: mismatched sockets"
      | Send s msg, Send s' msg' => fun k x =>
        if (socket_eqb s s' && message_eqb msg msg')%bool then
          match_trace' t' (k x)
        else
          fail "match_trace: mismatched sockets or messages"
      | _, _ => fun _ _ => fail "match_trace: mismatched events"
      end k x
    end
  | Ret v => match v with end
  end.

Definition trace_preorder (gen_fuel : nat) (match_fuel : nat)
           (p : itree specE void) (q : itree specE void)
  : Checker :=
  checker (bindGen (gen_trace gen_fuel p)
                   (fun t => collect (List.length t) (
                      match t with
                      (* Empty traces are trivially covered. *)
                      | [] => checker tt
                      | e' :: t' =>
                        check_spec match_fuel
                                   (match_trace (e', t') q)
                                   match_fuel
                      end))).

(*
(* Track all states simultaneously: inefficient!!! *)
(* Trace preorder: traces in [p] are a subset of the union
   of traces in [qs]. *)
CoFixpoint trace_preorder'
           (p : itree specE void) (qs : list (itree specE void))
  : itree (testE +' networkE') unit :=
  match p with
  | Tau p' => Tau (trace_preorder' p' qs)
  | Vis _ ep kp =>
    trace ("Step: " ++ show ep);;
    match ep with

    (* The absence of transition vacuously satisfies
       trace preorder. *)
    | (| Fail _ ) => Ret tt

    (* [(A + B) -> C] iff [A -> C] or [B -> C]. *)
    | (| _Or_p |) =>
      match _Or_p in nondetE T return (T -> _) -> _ with
      | Or => fun kp => Vis Or_ (fun b => trace_preorder' (kp b) qs)
      end kp

    (* [p] has a [networkE] effect, look for a match in [qs]. *)
    | ( ep ||) =>
      let k' z :=
          match match_effect' ep z qs with
          | [] => fail "trace_eq: no matching effect"
          | qs' => trace_preorder' (kp z) qs'
          end in
      Vis (| ep ) k'
    end

  | Ret v => match v with end
  end.

Definition trace_preorder p q := trace_preorder' p [q].
 *)

End TraceEquivalence.

(* ... and we can run it with QuickChick. *)
Definition test (imp : itree specE void) (spec : itree specE void)
  : Checker :=
  let gen_fuel := 50 in
  let match_fuel := 200 in
  let lively_fuel := 10 in

  let imp := collapse 100 imp in
  let spec := lively lively_fuel (collapse 100 spec) in

  let preordered imp spec :=
      trace_preorder gen_fuel match_fuel
                     imp spec in

  checker (
      bindGen arbitrary
              (fun b : bool =>
                 if b then
                   (* imp "simulates" spec *)
                   label "imp<spec" (preordered imp spec)
                 else
                   (* spec "simulates" imp *)
                   label "spec<imp" (preordered spec imp))).

Section SomeTests.

Definition server_impl (bug : Socket.variant) : itree specE void :=
  InterpretAPI.main_interpreted socket_eqb bug.

Definition server_spec (bug : HLS.variant) : itree specE void :=
  HLS.server_process bug.

Definition sampl__ : list (list nat) :=
  map (fun n =>
         map (fun z => List.length z)
             (sample (gen_trace n (collapse 100 (server_impl Socket.Fine))))) [25;50;100;200;400].

Definition server_test
           (imp_bug : Socket.variant)
           (spec_bug : HLS.variant)
: Checker :=
  test (server_impl imp_bug) (server_spec spec_bug).

Definition good_test : Checker :=
  server_test Socket.Fine HLS.Fine.

Definition imp_drop_send_test : Checker :=
  server_test Socket.DropSend HLS.Fine.

Definition imp_two_send_test : Checker :=
  server_test Socket.TwoSend HLS.Fine.

Definition spec_drop_send_test : Checker :=
  server_test Socket.Fine HLS.DropSend.

Definition spec_two_send_test : Checker :=
  server_test Socket.Fine HLS.TwoSend.

End SomeTests.
End TestSpecSection.
End TestSpec.

(* QuickChick good_test. *)

Module TraceSem.
Module HLS := HighLevelSpec.
Import TestSpec.
Section TraceSemSection.

(* The [Trace.T] type corresponds more closely to the
   idea of a trace, by annotating every event with one or
   more resulting values. *)

(* Counters are used to generate sockets and messages. *)
Definition clab E :=
  counterE (nat' socket) +' counterE (nat' message) +' labeledE E.

Definition label `{Convertible E F} {X} (e : E X) (xs : list X)
  : itree (clab F) X :=
  liftE (convert (Label (convert e) xs)).

Definition labelNetworkE `{Convertible networkE' E} X
           (e : networkE' X) : itree (clab E) X :=
  match e with
  | HLS.Accept =>
    s' <- incr;;
    let '(Tagged s) := s' : nat' socket in
    label HLS.Accept [s]
  | HLS.Recv s =>
    m' <- incr;;
    let '(Tagged m) := m' : nat' message in
    label (HLS.Recv s) [show m]
  | HLS.Send s m => label (HLS.Send s m) [tt]
  end.

Definition labelSpecE X (e : specE X) : itree (clab specE) X :=
  match e with
  | (| _Fail ) =>
    match _Fail with
    | Fail s => label (Fail s) []
    end
  | (| _Or |) =>
    match _Or with
    | Or => label Or [true; false]
    end
  | ( e ||) => labelNetworkE e
  end.

Definition traceSpec X (m : itree specE X) : T specE X :=
  MtoT 100 (run_counter_for socket (run_counter_for message (hom labelSpecE m))).

End TraceSemSection.
End TraceSem.

Module HighLevelCoSpec.
Module HLS := HighLevelSpec.
Section HighLevelCoSpecSection.

(*  *)

Variable socket : Type.
Variable message : Type.

Context `{Show socket} `{Arbitrary socket}.
Context `{Show message} `{Arbitrary message}.

Variable message_eqb : message -> message -> bool.

Inductive networkCE : Type -> Type :=
| CoAccept : socket -> networkCE unit
| CoRecv : socket -> message -> networkCE unit
| CoSend : socket -> networkCE message.

Definition coSpecE := Spec.specE +' networkCE.

Section NetworkCoCommands.

Context `{Convertible networkCE E}.

Definition coaccept (s : socket) : itree E unit :=
  liftE (convert (CoAccept s)).
Definition corecv (s : socket) (m : message) : itree E unit :=
  liftE (convert (CoRecv s m)).
Definition cosend (s : socket) : itree E message :=
  liftE (convert (CoSend s)).

End NetworkCoCommands.

(* Server description. *)

Definition conn_state := HLS.conn_state message.
Definition connection := HLS.connection socket message.

Definition handle_pending (pending : list connection)
  : itree coSpecE (list connection) :=
  (* Take any one element [conn] out of the pending queue.
     [pending']: remaining elements. *)
  p <- choose (select pending);;
  let '(conn, pending') := p in
  match HLS.st conn with
  | HLS.RECVING =>
    msg <- arb;;
    corecv (HLS.fd conn) msg;;
    let conn' := {|
          HLS.fd := HLS.fd conn;
          HLS.st := HLS.SENDING msg |} in
    ret (conn' :: pending')
  | HLS.SENDING msg =>
    msg' <- cosend (HLS.fd conn);;
    if message_eqb msg msg' then
      ret pending'
    else
      fail "Mismatched messages"
  end.

Definition poll (pending : list connection)
  : itree coSpecE (list connection) :=
  fd <- arb;;
  coaccept fd;;
  ret ({| HLS.fd := fd; HLS.st := HLS.RECVING |} :: pending).

CoFixpoint server_loop (pending : list connection)
  : itree coSpecE void :=
  pending' <- or (handle_pending pending) (poll pending);;
  server_loop pending'.

CoFixpoint server_process : itree coSpecE void :=
  server_loop [].

End HighLevelCoSpecSection.
End HighLevelCoSpec.

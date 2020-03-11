
From ExtLib.Structures Require Functor Applicative Monad.
From ITree Require Import
     ITree
     Basics.Basics
     Events.State.

From Coq Require Import Lists.List
     String.

Require Import NetworkTypes.
Require Import DeepWeb.Lib.Socket DeepWeb.Lib.SocketInterface DeepWeb.Lib.Util Map DeepWeb.Lib.NetworkInterface.

Import SocketAPI. 
Import ListNotations.

(** *Modeling network relevant I/O operations.

  (An experiment.)
  ""Relevant"" events and effects were crafted from the Network.Socket
  library documentation.

   https://hackage.haskell.org/package/network-3.1.1.1/docs/Network-Socket.html

 *)

Definition Socket := sockfd.

(* ====================================================== *)
(** *Haskell Network Events

   Network.v defines the corresponding embeddings of
   these uninterpreted events into ITrees.

   These are "axiomiatized" translations of relevant network effects, which
   can be automatically generated.
 *)
Inductive haskE : Type -> Type :=
| SendE : Socket -> bytes -> haskE Num.Int
| CloseE : Socket -> haskE unit
| AcceptE : Socket -> haskE (Socket * SockAddr)
| ListenE : Socket -> Num.Int -> haskE unit
| BindE : Socket -> SockAddr -> haskE unit
| SocketE : Family -> SocketType -> Num.Int -> haskE Socket
| SetSocketOptionE : Socket -> SocketOption -> Num.Int -> haskE unit.

(* ====================================================== *)
(** *Composing IO Events

   Alternatively, if we wanted to model _different IO events_, we can
   use the sum operator to combine different events.

   For instance, we can define the following:

   (* Read/write event to STDIN. *)
   Inductive rwE : Type -> Type :=
   | ReadEff : rwE unit
   | WriteEff : rwE unit
   .

   Definition ioE := rwE +' networkE.

   Using subevents, we can also compose different events. For now, we
   only focus on single-threaded network events.
 *)
Require Import ITree.Events.Nondeterminism ITree.Events.Exception.

Section OpenUnion.
  Generalizable Variables A B C D E.
  Class Convertible (A B : Type -> Type) :=
    { convert : forall {X}, A X -> B X }.

  (* Don't try to guess. *)
  Instance fluid_id A : Convertible A A | 0 :=
    { convert X a := a }.

  (* Destructure sums. *)
  Instance fluid_sum `{Convertible A C} `{Convertible B C}
    : Convertible (sum1 A B) C | 7 :=
    { convert X ab :=
        match ab with
        | inl1 a => convert a
        | inr1 b => convert b
        end }.

  (* Lean left by default for no reason. *)
  Instance fluid_left `{Convertible A B} C
    : Convertible A (sum1 B C) | 8 :=
    { convert X a := inl1 (convert a) }.

  (* Very incoherent instances. *)
  Instance fluid_right `{Convertible A C} B
    : Convertible A (sum1 B C) | 9 :=
    { convert X a := inr1 (convert a) }.

  Instance fluid_empty A : Convertible void1 A :=
    { convert X v := match v with end }.

  Definition lift {E F X} `{Convertible E F} : itree E X -> itree F X :=
    @translate _ _ (@convert _ _ _) _.

  Class Embed X Y :=
    { embed : X -> Y }.

  Instance Embed_fun A X Y `{Embed X Y} : Embed (A -> X) (A -> Y) :=
    { embed := fun x a => embed (x a) }.

  Instance Embed_eff E F X `{Convertible E F} : Embed (E X) (itree F X) :=
    { embed := fun e => trigger (convert e) }.

  Arguments embed {X Y _} e.

End OpenUnion.

  Notation "E -< F" := (Convertible E F)
  (at level 92, left associativity) : type_scope.

  Definition or {E X} `{nondetE -< E} (k1 k2 : itree E X) : itree E X :=
    Vis (convert Or) (fun x : bool => if x then k1 else k2).

Definition ioE := haskE +' (exceptE string) +' nondetE.

Definition IO := itree ioE.

(* ====================================================== *)
(** *Specification of simple server *)
(* ====================================================== *)
From DeepWeb.Lib Require Import Util LinearSpec_Traces LinearSpec_Server.
From ITree Require Import Traces.

Require Import Coq.ZArith.ZArith.
From Custom Require Import String.

Definition BUFFER_SIZE : Z := 1024.
Definition SERVER_PORT : endpoint_id := Endpoint 8000.
Definition INIT_MSG := repeat_string "0"%char (Z.to_nat BUFFER_SIZE).

Module App.
Record t : Type := {
  req_size : nat; (* May be replaced with a parser *)
  state : Type;
  initial_state : state;
  app : state * string -> state * string;
}.
End App.

Module Config.
Record t : Type := {
  req_size : nat;
  initial_state : string;
}.
End Config.

Import App.

Definition server_app (config: Config.t): App.t :=
  {|
    req_size := Config.req_size config;
    state := string;
    initial_state := Config.initial_state config;
    app := fun '(msg) => (msg);
  |}.

Definition real_app_config : Config.t :=
  {|
    Config.req_size := Z.to_nat BUFFER_SIZE;
    Config.initial_state := INIT_MSG;
  |}.

Definition real_app := server_app real_app_config.

(* ====================================================== *)
(** *Specification of simple server *)
(* ====================================================== *)

From DeepWeb Require Import Spec.Swap_ImplModel.

(* ====================================================== *)
(* Network events are not compatible with our haskE, because in order to handle
   these, we have to match the return types (which are not defined in the same
   way..) *)
(* Variant networkE : Type -> Type := *)
(* | Listen : endpoint_id -> networkE unit *)
(* | Accept : endpoint_id -> networkE connection_id *)
(* | Shutdown : connection_id -> networkE unit *)
(* | RecvByte : connection_id -> networkE byte *)
(* | SendByte : connection_id -> byte -> networkE unit. *)

Section Impl.

  Variable (app : App.t).

  (* Super sketchy subevent handling... This "convert" seems to be too lenient. *)
  Context `{nondetE -< ioE}.
  Context `{networkE -< ioE}.
  Import Monad.MonadNotation.

  Definition send_bytes (c : connection_id) (str : string) : IO.IO unit :=
    ITree.iter (fun x : string => match x with
                               | EmptyString => Ret (inr tt)
                               | String a kx =>
                                 Vis (convert (SendByte c a)) (fun _ => Ret (inl x))
                               end
               ) str.

  (* runConn :: (Socket, SockAddr) -> IO () *)
  (* runConn (sock, _) = do *)
  (*   send sock "Hello World!\n" *)
  (*   close sock *)

  (* runConn specification using networkE and nondetE. networkE is less expressive
     than haskE (for instance, the "Close" and "Shutdown" are not distinguished.
  *)
  Definition runConn (sock : Socket) (addr : NetworkTypes.SockAddr) (sm : SocketMap)
    : IO.IO (unit * SocketMap) :=
    or (match connection_of_fd sm sock with (* Successful communication. *)
        | Some x => ITree.bind (send_bytes x "Hello World")
                     (fun _ => Vis (convert (Shutdown x)) (fun _ => Ret (tt, sm)))
        | None => Ret (tt, sm) (* Failed communication. *)
        end)
       (Ret (tt, sm)) (* Failed communication. *)
  .

  (* mainLoop :: Socket -> IO () *)
  (* mainLoop sock = do *)
  (*   conn <- accept sock     -- accept a connection and handle it *)
  (*   runConn conn            -- run our server's logic *)
  (*   mainLoop sock           -- repeat *)
  (* Definition mainLoop : NetworkTypes.Socket -> IO.IO unit := *)
  (* fun (sock : NetworkTypes.Socket) => *)
  (*   (@ITree.forever IO.ioE unit unit (Network_.accept sock GHC.Base.>>= *)
  (*     (fun conn => runConn conn))). *)

  (* We can't use DeepWeb to reason about Sockets, because the logic that deals
     with creating an "observable oracle" and observing only connection events
     is handled through VST. *)
  (* Definition mainLoop (sock : Socket) (sm : SocketMap) : IO.IO (unit * SocketMap) := *)
  (*   match endpoint_of_fd sm sock with *)
  (*   | Some x => accept_connection x *)
  (*   | None => Ret tt *)
  (*   end *)
  (* . *)

End Impl.

(* ====================================================== *)
(** *Trace Refinement*)
(* ====================================================== *)

(* We could get "high-level" traces that are reorderable. *)
(* DeepWeb's definition of "high-level" is on hiding the abstraction of
   concurrent and nondeterministic effects. Unfortunately, we still have no way
   of getting rid of those from our source Haskell program so we can't use these
   for now.
 *)
Definition real_trace := @trace (LinearSpec_Traces.event) byte.

Require Import Coq.Strings.Ascii.
Local Open Scope char_scope.

Definition network_event_response (e : real_event) (tr : trace) :=
  match e with
    | NewConnection id =>
      (TEventEnd e)
    | ToServer id b =>
      (TEventResponse e b tr)
    | FromServer id b =>
      (@TEventResponse LinearSpec_Traces.event byte _ e b tr)
  end.

Inductive network_reordered_ :
   LinearSpec_NetworkModel.network_state -> real_trace -> real_trace -> Prop :=
  | ScrambleEmpty : forall ns : LinearSpec_NetworkModel.network_state,
                    network_reordered_ ns TEnd TEnd
  | ScrambleServer : forall (ns ns' : LinearSpec_NetworkModel.network_state)
                       (e : real_event) (tr_server tr_client : trace),
                     server_transition e ns ns' ->
                     network_reordered_ ns' tr_server tr_client ->
                     network_reordered_ ns (network_event_response e tr_server)
                                        tr_client
  | ScrambleClient : forall (ns ns' : LinearSpec_NetworkModel.network_state)
                       (e : real_event) (tr_server tr_client : real_trace),
                     client_transition e ns ns' ->
                     network_reordered_ ns' tr_server tr_client ->
                     network_reordered_ ns tr_server
                                        (network_event_response e tr_client).

Definition network_reordered := network_reordered_ LinearSpec_NetworkModel.initial_ns.

(* ====================================================== *)
(** Experiment: Handling into stateT.
    (Seems inappropriate for modeling nondeterministic and concurrent behavior.) *)
(* ====================================================== *)
(** *Network World state
(* ====================================================== *)
   We take the conventional perspective of viewing the IO monad
   as handling effects in the effectful (awkward) _World_, following
   DeepWeb network model representation.
   (https://github.com/DeepSpec/DeepWeb/blob/master/src/MiniSwap/Lib/LinearSpec_Interface.v)
 *)

Section World.
(* A couple axioms along the way... *)

  (* Assume decidable boolean equality check exists between Sockets. *)
  Axiom socket_eq : forall (x y : Socket), {x=y}+{x<>y}.
  Axiom socket_eqb : Socket -> Socket -> bool.
  Infix "/=?" := socket_eqb (at level 50).
  (* Assume there is a function that generates new SockAddrs and Sockets.
    (For `accept`.) *)
  Axiom newSockAddr : unit -> SockAddr.
  Axiom newSock : unit -> Socket.

  Definition valid_socket (sl : list Socket) (x : Socket) : bool :=
    match (List.find (socket_eqb x) sl) with
    | Some _ => true
    | _ => false
    end
  .

  Notation stateT := ITree.Basics.Basics.Monads.stateT.

  Variable (app : App.t).

  Definition world : Type := SocketMap * list connection * state app.

  Definition handle_send (w : world) (sock : Socket) (b : bytes) :
    world * Num.Int :=
    let '(sm, conns, app) := w in
    match connection_of_fd sm sock with
    | Some _ => ((sm, conns, app), 1%Z)
    | None => ((sm, conns, app), 0%Z)
    end
  .

  Definition remove_conn (c : connection_id) (cl : list connection) :=
    cl (* TODO: Filter. *).

  Definition handle_close (w : world) (sock : Socket) : world :=
    let '(sm, conns, app) := w in
    match connection_of_fd sm sock with
    | Some x => (sm, remove_conn x conns, app)
    | None => w
    end
  .

  (* TODO: Implement these handle functions. *)
  Definition handle_accept (w : world) (sock : Socket) :
    world * (Socket * SockAddr) :=
    (w, (sock, newSockAddr tt)).

  Definition handle_listen (w : world) (sock : Socket) (n : Num.Int) : world := w.

  Definition handle_bind (w : world) (sock : Socket) (addr : SockAddr) : world := w.

  Definition handle_socket (w : world) : world * Socket :=
    (w, newSock tt).

  Definition handle_setSocketOption (w : world) : world := w. 

  (* To model the world state, we wish to interpret these events into a
    stateT monad with world information. *)
  Definition h_network {E} : haskE ~> stateT world (itree E) :=
    fun _ e w =>
      match e with
      | SendE s b => Ret (handle_send w s b)
      | CloseE s => Ret (handle_close w s, tt)
      | AcceptE s => Ret (handle_accept w s)
      | ListenE s n => Ret (handle_listen w s n, tt)
      | BindE s a => Ret (handle_bind w s a, tt)
      | SocketE _ _ _ => Ret (handle_socket w)
      | SetSocketOptionE f s n => Ret (handle_setSocketOption w, tt)
      end.

  (* Old version... *)
  (*       if valid_socket skt s then *)
  (*         Ret ((sm, clnt, skt, (s, x)::msgs), 1% Z) *)
  (*       else *)
  (*         Ret ((srv, clnt, skt, msgs), 0%Z) *)
  (*     | CloseE s => *)
  (*       if valid_socket skt s then *)
  (*         Ret ((srv, clnt, remove socket_eq s skt, msgs), tt) *)
  (*       else *)
  (*         Ret ((srv, clnt, skt, msgs), tt) *)
  (*     | AcceptE s => *)
  (*       if valid_socket skt s then *)
  (*         match srv with *)
  (*         | (ls, n, true) => *)
  (*           if length ls <? n then *)
  (*             Ret (((s::ls, n, true), clnt, skt, msgs), (s, newSockAddr tt)) *)
  (*           else *)
  (*             Ret (((s::(removelast ls), n, true), clnt, skt, msgs), *)
  (*                 (s, newSockAddr tt)) *)
  (*         | (_, _, _) => (Ret ((srv, clnt, skt, msgs), (s, newSockAddr tt))) *)
  (*         end *)
  (*       else *)
  (*         Ret ((srv, clnt, skt, msgs), (s, newSockAddr tt)) *)
  (*     | ListenE s n => (* ListenE mutates "global" connection max count... *) *)
  (*       if valid_socket skt s then *)
  (*         match srv with *)
  (*         | (ls, _, false) => Ret (((ls, Z.to_nat n, true), clnt, skt, msgs), tt) *)
  (*         | (_, _, _) => Ret ((srv, clnt, skt, msgs), tt) *)
  (*         end *)
  (*       else *)
  (*         Ret ((srv, clnt, skt, msgs), tt) *)
  (*     | BindE s a => *)
  (*       if valid_socket skt s then *)
  (*         match srv with *)
  (*         | (ls, _, true) => Ret ((srv, clnt, skt, msgs), tt) *)
  (*         | (_, _, _) => Ret ((srv, clnt, skt, msgs), tt) *)
  (*         end *)
  (*       else *)
  (*         Ret ((srv, clnt, skt, msgs), tt) *)
  (*     (* Takes in dummy socket generator... *) *)
  (*     | SocketE _ _ _ => Ret ((srv, clnt, (newSock tt)::skt, msgs), newSock tt) *)
  (*     (* Ignore this Socket representation, for now. *) *)
  (*     | SetSocketOptionE f s n => Ret ((srv, clnt, skt, msgs), tt) *)
  (*     end *)
  (* . *)

  (* Since there is only one event type (network), handling IO is equivalent to
    handling networks. *)
  Definition h_io {E} : ioE ~> stateT world (itree E) := h_network.

  Definition interp_io {E A} (t : itree ioE A) : stateT world (itree E) A :=
    interp h_io t.

End World.

(* ====================================================== *)
(* Functor/Applicative/Monad laws, taken from wc example. *)

Section Functors.

  Variable f : Type -> Type.

  Context `{Functor.Functor f}.

  Global Instance Functor_Functor : Functor f :=
    fun _ X =>
      X {| fmap__ := fun a b : Type => Functor.fmap;
           op_zlzd____ := fun a b : Type => Functor.fmap ∘ const
        |}.

  Section Applicatives.

    Context `{Applicative.Applicative f}.

    Global Instance Applicative_Applicative : Applicative f :=
      fun _ X =>
        X {| liftA2__ := fun a b c f x y => Applicative.ap (fmap f x) y;
             op_zlztzg____ := fun a b => Applicative.ap ;
             op_ztzg____ := fun a b x y => Applicative.ap (id <$ x) y;
             pure__ := fun a => Applicative.pure
          |}.

    Section Monads.

      Context `{Monad.Monad f}.

      Global Instance Monad_Monad : Monad f :=
        fun _ X =>
          X {| op_zgzg____ := fun a b x y => Monad.bind x (fun _ => y);
               op_zgzgze____ := fun a b => Monad.bind ;
               return___ := fun a => Monad.ret
            |}.

    End Monads.
  End Applicatives.
End Functors.

Instance Functor_IO : Functor IO := Functor_Functor IO.
Instance Applicative_IO : Applicative IO := Applicative_Applicative IO.
Instance Monad_IO : Monad IO := Monad_Monad IO.

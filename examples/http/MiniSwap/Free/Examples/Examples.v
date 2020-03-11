Set Warnings "-extraction-opaque-accessed,-extraction".
Set Bullet Behavior "Strict Subproofs".

Set Implicit Arguments.
Set Contextual Implicit.

Require Import Bool.
Require Import Strings.Ascii.

From QuickChick Require Import QuickChick.

From Custom Require Import
     String.

Require DeepWeb.Free.Monad.Free.
Require Import DeepWeb.Free.Monad.Verif.
Require Import DeepWeb.Free.Monad.Common.
Require Import DeepWeb.Free.Monad.Concurrent.
Require DeepWeb.Free.Monad.IO.
Require DeepWeb.Free.Monad.Spec.

Require ProofIrrelevance.

Import SumNotations.
Open Scope sum_scope.

Module MONAD := Monad.Free.
Module IO := Monad.IO.IO.
Module SPECMONAD := Monad.Spec.

Definition null {A} (xs : list A) :=
  match xs with
  | nil => true
  | _ => false
  end.

Definition value : Set := string.

(** A simple demonstration of the machinery from above... *)

Module IOTEST.
Export IO.
Export SPECMONAD.

Definition IO := @IO value.

Inductive CoIOEvent : Type -> Type :=
| ProvideInput : value -> CoIOEvent unit
| ConsumeOutput : CoIOEvent value.

Definition IOSpec := itree (specE +' CoIOEvent).

Definition consume_output : IOSpec value :=
  liftE (convert ConsumeOutput).
Definition provide_input (v : value) : IOSpec unit :=
  liftE (convert (ProvideInput v)).

Definition zip_prog_test A : IO void -> IOSpec A -> PureSpec A :=
  fun m1 m2 =>
    let zip A B (e : IOEvent A) (ce : CoIOEvent B) :=
        match e in IOEvent X, ce in CoIOEvent Y return PureSpec (X * Y) with
        | Output v, ConsumeOutput =>
          trace ("output " ++ v);;
          Ret (tt, v)
        | Input, ProvideInput v =>
          trace ("input " ++ v);;
          Ret (v, tt)
        | _, _ => fail "zip_prog_test: mismatch"
        end
          in mapM (fun a' : void + A => match a' with
                             | inl v => match v with end
                             | inr a => a : A
                             end)
            (zipM zip (lift m1) m2).

Ltac appRule c :=
  rewrite matchM; apply c;
  intros;
  repeat (rewrite matchM; apply vt_tau).

Definition myprog (u: unit): IO void :=
  x <- recv ;;
  y <- recv ;;
  send y ;;
  send x ;;
  send "Done!" ;;
  spin.

Definition myprog0 (u: unit) : IO void :=
  x <- recv ;;
  forever (send x).

CoFixpoint myprog1 (u: unit): IO void :=
  x <- recv ;;
  if (string_dec x "a") then
    forever (send x)
  else myprog1 u.

(* Compute runIO myprog1 ["foo"; "bar"; "baz"; "a"] 100. *)

CoFixpoint myprog2 (u: unit): IO void :=
  x <- recv ;;
  send x ;;
  myprog2 u.

(* Copy of myprog2, eta-expanded with a fake parameter,
   as otherwise the code generator produces invalid Ocaml *)
CoFixpoint myprog2' (u: unit) : IO void :=
  x <- recv ;;
  send x ;;
  myprog2' u.

CoFixpoint myprog3 (u: unit): IO void :=
  x <- recv ;;
  y <- recv ;;
  send y ;;
  send x ;;
  myprog3 u.

CoFixpoint myprog4 (u: unit) : IO void :=
  x <- recv ;;
  y <- recv ;;
  send (x++y)%string ;;
  myprog4 u.

CoFixpoint parrot_spec (l: list value) : IOSpec void :=
  alt
    (v <- consume_output ;;
     if List.existsb (string_eq v) l
     then parrot_spec l
     else fail "parrot_spec: fail")
    (v <- arb ;;
     provide_input v ;;
     parrot_spec (v::l)).

Lemma verify_prog0_parrot :
  valid_spec (zip_prog_test (myprog0 tt) (parrot_spec [])).
Proof.
  rewrite matchM.
  apply alt_r.
  rewrite matchM.
  apply vt_arb.
  intro v.
  repeat (rewrite matchM; apply vt_tau).
Abort. (* TODO *)
(*
  change (valid_spec (zip_prog_test (forever (send v)) (parrot_spec [v]))).
  cofix.
  rewrite matchM; apply or_l.
  repeat (rewrite matchM; apply vt_tau).
  simpl; rewrite string_eq_refl.
  apply verify_prog0_parrot.
Qed. *)

Lemma verify_prog2_parrot :
  valid_spec (zip_prog_test (myprog2 tt) (parrot_spec [])).
Proof.
  generalize ([] : list value).
  cofix.
  intros.
  rewrite matchM; apply alt_r.
  rewrite matchM; apply vt_arb; intro.
  repeat (rewrite matchM; apply vt_tau).
Abort. (* TODO *)
(*
  rewrite matchM; apply or_l.
  repeat (rewrite matchM; apply vt_tau).
  simpl. rewrite string_eq_refl.
  apply verify_prog2_parrot.
Qed.
*)

Lemma check3 : valid_spec (zip_prog_test (myprog3 tt) (parrot_spec [])).
Proof.
  generalize ([] : list value).
  cofix.
  intros.
  appRule alt_r.
  appRule (@vt_arb void).
Abort. (* TODO *)
(*
  appRule or_r.
  appRule vt_arb.
  appRule or_l.
  replace (List.anyb _ _) with true.
  appRule or_l.
  replace (List.anyb _ _) with true.
  apply check3.

  (* Side conditions *)
  simpl. destruct (string_eq v v0); auto; rewrite string_eq_refl; auto.
  simpl. rewrite string_eq_refl; auto.
Qed.
*)

End IOTEST.

(* ========================================================================= *)

(* Run some tests. Needs to be outside a Module because otherwise QuickCheck barfs. *)

Import IO.
Import IOTEST.

(* N.b.: We can't extract cofixpoints with no parameters *)

(* QuickChick (check_spec 100 (zip_prog_test myprog0 (parrot_spec []))). *)
(* Needs eta expansion
QuickChick (check_spec 100 (myprog2' tt) (parrot_spec [])).
QuickChick (check_spec 100 (myprog3 (parrot_spec [])).
*)
(* QuickChick (check_spec 100 (zip_prog_test (myprog4 tt) (parrot_spec []))). *)

(* ========================================================================= *)
(* ========================================================================= *)
(* ========================================================================= *)

(** A single-cell storage "application." *)

Module ONECELLSTOREAPP.

Definition etag := value.
Definition app_state := value.

Inductive req := PUT (v : value) | GET (ot : option etag).

Derive Show for req.
Derive Arbitrary for req.

Inductive res := PUTr | GETr (tag: etag) (ov : option value).
Derive Show for res.

(* TODO: Investigate whether it's better to combine these into one. *)
Definition execute (r : req) (s : app_state) : app_state :=
  match r with
    PUT v => v
  | GET ot => s
  end.

Open Scope string_scope.

Definition hash s := "ETAG" ++ s.

Definition respond (r : req) (s : app_state) : res :=
  match r with
    PUT v => PUTr
  | GET None => GETr (hash s) (Some s)
  | GET (Some t) => if (hash s) = t ? then GETr (hash s) None else GETr (hash s) (Some s)
  end.

(* A wrong one... *)
Definition respond' (r : req) (s : app_state) : res :=
  match r with
    PUT v => PUTr
  | GET None => GETr (hash s) (Some s)
  | GET (Some t) => GETr (hash s) (Some s)
  end.

Instance dec_eq_res (p1 p2 : res) : Dec (p1 = p2).
Proof. dec_eq. Defined.
Hint Resolve dec_eq_res : eq_dec.

End ONECELLSTOREAPP.

(* ========================================================================= *)
(* A very simple version of the HTTP server library... *)

Require Import Arith.

Module HTTPSERVERMONAD.  (* TODO: Drop MONAD here and some other places :-) *)

Export MONAD.
Export ONECELLSTOREAPP.  (* Maybe app_state, execute, respond should be parameters? *)

Instance dec_eq_res (p1 p2 : nat * res) : Dec (p1 = p2).
Proof. dec_eq. Defined.

(* These nats are sequence numbers, used to match up responses to their requests. *)
Definition request := (nat * req)%type.
Definition result := (nat * res)%type.

Inductive HTTPEvent : Type -> Type :=
| Wait : HTTPEvent request
| Reply : result -> HTTPEvent unit.

Definition Server := itree HTTPEvent.

Definition wait : Server request :=
  Vis Wait (fun v => Ret v).
Definition reply (r : res) (n : nat) : Server unit :=
  Vis (Reply (n, r)) (fun v => Ret v).

(* TODO: Fix ,, *)
(*Notation " x ,, y  <- c1 ;; c2" := (@pbind _ _ _ _ _ c1 (fun xy => let (x, y) := xy in c2))
    (at level 100, c1 at next level, right associativity) : monad_scope.
*)

(** A bunch of correct and incorrect servers... *)

CoFixpoint server (s : app_state) : Server void :=
  request <- wait ;;
  let (id, req) := request in
  let s' := execute req s in
  reply (respond req s) id ;;
  server s'.

CoFixpoint server_stutter (s : app_state) : Server void :=
  request <- wait ;;
  let (id, req) := request in
  let s' := execute req s in
  reply (respond req s) id ;;
  reply (respond req s) id ;;
  server_stutter s'.

CoFixpoint bad_server1 (s1 s2 : app_state) : Server void :=
  request <- wait ;;
  let (id, req) := request in
  let s2' := execute req s2 in
  reply (respond req s1) id ;;
  bad_server1 s2 s2'.

CoFixpoint drop_every_2nd_server (s : app_state)
  : Server void :=
  request1 <- wait ;;
  let (id1, req1) := request1 in
  let s' := execute req1 s in
  request2 <- wait ;;
  let (id2, req2) := request2 in
  let s'' := execute req2 s' in
  reply (respond req1 s) id1 ;;
  drop_every_2nd_server s''.

CoFixpoint server_delayed (s : app_state) : Server void :=
  request1 <- wait ;;
  let (id1, req1) := request1 in
  let s' := execute req1 s in
  request2 <- wait ;;
  let (id2, req2) := request2 in
  let s'' := execute req2 s' in
  reply (respond req1 s) id1 ;;
  reply (respond req2 s') id2 ;;
  server_delayed s''.

(* Interesting bug! *)
CoFixpoint server_delayed_wrong (s : app_state) : Server void :=
  request1 <- wait ;;
  let (id1, req1) := request1 in
  let s' := execute req1 s in
  request2 <- wait ;;
  let (id2, req2) := request2 in
  let s'' := execute req2 s' in

  reply (respond req1 s) id1 ;;
  reply (respond req2 s) id2 ;;

  server_delayed_wrong s''.

CoFixpoint server_delayed_wrong2 (s : app_state) : Server void :=
  request1 <- wait ;;
  let (id1, req1) := request1 in
  let s' := execute req1 s in
  request2 <- wait ;;
  let (id2, req2) := request2 in
  let s'' := execute req2 s' in

  reply (respond req1 s'') id1 ;;
  reply (respond req2 s'') id2 ;;

  server_delayed_wrong2 s''.

CoFixpoint server_reorder (s : app_state) : Server void :=
  request1 <- wait ;;
  let (id1, req1) := request1 in
  let s' := execute req1 s in
  request2 <- wait ;;
  let (id2, req2) := request2 in
  let s'' := execute req2 s' in
  reply (respond req2 s') id2 ;;
  reply (respond req1 s) id1 ;;
  server_reorder s''.

End HTTPSERVERMONAD.

(* ========================================================================= *)

Module HTTPSERVERSPEC.
Export SPECMONAD.
Export HTTPSERVERMONAD.

Inductive CoHTTPEvent : Type -> Type :=
| Send    : req -> CoHTTPEvent nat
| Receive : CoHTTPEvent (nat * res).

Definition HTTPSpec := itree (specE +' CoHTTPEvent).

Definition send {E} `{Convertible CoHTTPEvent E} (r : req)
  : itree E nat := liftE (convert (Send r)).
Definition receive {E} `{Convertible CoHTTPEvent E}
  : itree E (nat * res) := liftE (convert Receive).

(* TODO: Some refactoring possible here... *)
Fixpoint pick_oneM_go {A} {E} (ys xs : list A) :  itree (specE +' E) (A * list A) :=
    match xs with
      | [] => fail "pick_oneM_go: no choice left"
      | (x :: xs') =>
          or (ret (x , ys ++ xs')%list)
             (pick_oneM_go (ys ++ [x])%list xs')
    end.


Definition pick_oneM {A} {E} (xs : list A) :  itree (specE +' E) (A * list A) :=
  pick_oneM_go [] xs.

Fixpoint anySpec {E R} (xs : list (itree (specE +' E) R)) :=
  match xs with
  | [] => fail "anySpec: no choice left"
  | x :: xs => or x (anySpec xs)
  end.

Definition spec_type : Type :=
  list req -> list (nat * req) -> app_state -> list (nat * res) ->
  HTTPSpec unit.

Definition spec_send (spec : spec_type) arb_req pending s expected :=
  match arb_req with
  | r :: arb_req' =>
    trace ("sending   " ++ show r);;
    n <- send r;;
    spec arb_req' ((n , r) :: pending) s expected
  | [] => fail "spec: no request to send"
  end.

Definition spec_exec (spec : spec_type) arb_req pending s expected :=
  p <- pick_oneM pending ;;
    match p with
    | ((n, req), pending') =>
      let s' := execute req s in
      let res := respond req s in
      spec arb_req pending' s' ((n, res) :: expected)
    end.

Definition spec_recv (spec : spec_type) arb_req pending s expected :=
  res <- receive ;;
  trace ("receiving " ++ show (snd res));;
  p <- pick_oneM expected ;;
  match p with
  | (res', expected') =>
    if res = res' ?
    then spec arb_req pending s expected'
    else fail ("spec: invalid response, got "
                 ++ show res' ++ ", expected "
                 ++ show res)
  end.

Definition spec_done : spec_type := fun arb_req pending s expected =>
  if (null arb_req
   && null pending
   && null expected)%bool
  then ret tt
  else fail "spec: unfinished business".

(** Simple specification that inserts "conjectured events" using Or --
    probably nicer for proving. *)
(* TODO: execute, respond should really be parameters to this *)
CoFixpoint spec
    (* Stream of requests generated by QC: *)
    (arb_req : list req)
    (* Requests that we've sent but that the server has not responded to: *)
    (pending : list (nat * req))
    (* Conjectured application state: *)
    (s : app_state)
    (* Responses that are "on the wire" (or in internal server
       buffers) but not yet received: *)
    (expected : list (nat * res))
  : HTTPSpec unit :=
  anySpec [
      spec_send spec arb_req pending s expected;
      spec_exec spec arb_req pending s expected;
      spec_recv spec arb_req pending s expected;
      spec_done arb_req pending s expected
    ].

(* Same thing, but uses [respond'] instead of [respond] *)
CoFixpoint wrong_etag_spec
    (pending_req : list (nat * req))
    (s : app_state)
    (expected_resp : list (nat * res))
    (arb_req : list req)
  : HTTPSpec unit :=
  or (match arb_req with
        | r :: arb_req' =>
          trace ("sending   " ++ show r);;
          n <- send r;;
          wrong_etag_spec ((n , r) :: pending_req) s expected_resp arb_req'
        | [] => spin
      end)
  (or (p <- pick_oneM pending_req ;;
      match p with ((n, req), pending_req') =>
        let s' := execute req s in
        let res := respond' req s in
        wrong_etag_spec (pending_req') s' ((n, res) :: expected_resp) arb_req
      end)
     (res <- receive ;;
      trace ("receiving " ++ show (snd res));;
      p <- pick_oneM expected_resp ;;
      match p with (res', expected_resp') =>
        if res = res' ?
        then wrong_etag_spec pending_req s expected_resp' arb_req
        else fail "wrong_etag_spec"
      end)).

(** A more sophisticated form of specifications using a data structure
    to keep track of sets of "conjectured states of the world" --
    nicer for testing. *)

Definition test_state :=
  (list (nat * req) (* Pending requests *) *
   app_state *
   list (nat * res) (* Expected responses *))%type.

Fixpoint pick_one_l {X} (xs : list X) : list (X * list X) :=
  match xs with
    | [] => []
    | x :: xs => (x, xs) :: map (fun p => match p with (y, ys) => (y, x :: ys) end) (pick_one_l xs)
  end.

Fixpoint next' (n : nat) (tss : list test_state) : list test_state :=
  match n with
    | 0 => []
    | S n' =>
      let tss' :=
        flat_map
          (fun ts => match ts with (prs, s, ers) =>
            map
              (fun p => match p with ((n, req), prs') =>
                let s':= execute req s in
                let res := respond req s in
                (prs', s',  ((n, res) :: ers))
               end)
            (pick_one_l prs)
          end)
          tss in
      tss ++ next' n' tss'
 end.

(* Apply any number of pending requests on the server *)
Definition next (ts : test_state) : list test_state :=
      match ts with (prs, s, ers) => next' (S (List.length prs)) [ts] end.

Definition enqueue (x : nat * req) (ts : test_state) : test_state :=
      match ts with (prs, s, ers) => (x :: prs, s, ers)  end.

Definition dequeue (r : nat * res) (ts : test_state) : list test_state :=
      match ts with (prs, s, ers) =>
        if List.existsb (fun x => x = r ?) ers
        then [(prs, s, filter (fun r' => r <> r' ?) ers)]
        else []
       end.

(* ...Note the simpler disjunction [than spec] -- only sending and
   receiving: *)
CoFixpoint spec2
    (arb_req : list req)
    (states : list test_state )
  : HTTPSpec unit :=
  anySpec [
      res <- receive ;;
      trace ("receiving (" ++ show (fst res) ++ "): " ++ show (snd res));;
      (* trace ("states:   " ++ show states) ;; *)
      let states' := flat_map next states in
      (* trace ("states':  " ++ show states') ;; *)
      let states'' := flat_map (dequeue res) states' in
      (* trace ("states'': " ++ show states'') ;; *)
      match states'' with
        | [] => fail "spec2: No states left"
        | _ => spec2 arb_req states''
      end;

      match arb_req with
        | r :: arb_req' =>
          n <- send r;;
          trace ("sending   (" ++ show n ++ "): " ++ show r);;
          spec2 arb_req' (map (enqueue (n, r)) states)
        | [] => fail "spec2: no requests to send"
      end;

      if (null arb_req
         && existsb (fun '(pending, _, expected) =>
                       null pending && null expected)
                    states)%bool
      then ret tt
      else fail "spec2: unfinished business"
    ].

Fixpoint etag_next' (n : nat) (tss : list test_state) : list test_state :=
  match n with
    | 0 => []
    | S n' =>
      let tss' :=
        flat_map
          (fun ts => match ts with (prs, s, ers) =>
            map
              (fun p => match p with ((n, req), prs') =>
                let s':= execute req s in
                let res := respond' req s in
                (prs', s',  ((n, res) :: ers))
               end)
            (pick_one_l prs)
          end)
          tss in
      tss ++ next' n' tss'
 end.

Definition etag_next (ts : test_state) : list test_state :=
      match ts with (prs, s, ers) => etag_next' (S (List.length prs)) [ts] end.

Definition tags_from_res r :=
  match r with
    PUTr => None
  | GETr t _ => Some t
  end.

Definition replace_tag r (usetag:nat) tags_seen :=
  match r with
  | PUT v => PUT v
  | GET None => GET None
  | GET (Some _) => match tags_seen usetag with
                      None => GET None   (* little bit wrong, arguably *)
                    | Some t => GET (Some t)
                    end
  end.

CoFixpoint wrong_etag_spec2
    (states : list test_state)
    (tags_seen : nat -> option etag)
    (conn_to_req_id : nat -> nat)
    (arb_req : list (nat * req * nat))
  : HTTPSpec unit :=
  or (res <- receive ;;
      let tags_seen' := fun n =>
                          if n = conn_to_req_id (fst res) ?
                          then tags_from_res (snd res) else tags_seen n in
      trace ("receiving (" ++ show (fst res) ++ "): " ++ show (snd res));;
      (* trace ("states:   " ++ show states) ;; *)
      let states' := flat_map etag_next states in
      (* trace ("states':  " ++ show states') ;; *)
      let states'' := flat_map (dequeue res) states' in
      (* trace ("states'': " ++ show states'') ;; *)
      match states'' with
        | [] => fail "wrong_etag_spec2"
        | _ => wrong_etag_spec2 states'' tags_seen' conn_to_req_id arb_req end)
     (match arb_req with
        | (rn, r, usetag) :: arb_req' =>
          let r' := replace_tag r usetag tags_seen in
          n <- send r';;
          trace ("sending   (" ++ show n ++ "): " ++ show r');;
          let conn_to_req_id' := fun x => if n = x ? then rn else conn_to_req_id x in
          wrong_etag_spec2 (map (enqueue (n, r)) states) tags_seen conn_to_req_id' arb_req'
        | [] => ret tt
      end).

(* TODO: One might wish to generalize this to put the nats in a monad
   passed as a parameter.  Not clear it would work, though, because of
   productivity. *)
CoFixpoint zipPS {A} (p : Server void) (t : HTTPSpec A) (n : nat) : PureSpec A :=
  match p, t with
    (* Tau, _ | _, Tau *)
    | Tau p', _ => Tau (zipPS p' t n)
    | _, Tau t' => Tau (zipPS p t' n)

    (* _, Trace *)
    | _, Vis _ ( trace' |||||) tk =>
      Vis (convert trace') (fun v => zipPS p (tk v) n)

    (* _, Arb *)
    | _, Vis _ (| arb' ||||) tk =>
      match arb' in arbitraryE T return (T -> _) -> _ with
      | Arb _ _ _ _ _ =>
        fun tk => Vis Arb_ (fun v => zipPS p (tk v) n)
      end tk

    (* _, Or *)
    | _, Vis _ (| or' ||) tk =>
      match or' in nondetE T return (T -> _) -> _ with
      | Or => fun tk => Vis Or_ (fun v => zipPS p (tk v) n)
      end tk

    (* Alt *)
    | _, Vis _ (| alt' |||) tk =>
      match alt' in altE T return (T -> _) -> _ with
      | Alt => fun tk => Vis Alt_ (fun v => zipPS p (tk v) n)
      end tk

    (* Fail *)
    | _, Vis _ (| Fail r |) _ =>
      fail ("zipPS: Fail " ++ show r)

    (* Wait, Send *)
    | Vis _ Wait pk,
      Vis _ (| e ) tk =>
      match e in CoHTTPEvent T return (T -> _) -> _ with
      | Send r => fun tk => Tau (zipPS (pk (n, r)) (tk n) (S n))
      | Receive => fun _ => fail "zipPS: Wait/Receive"
      end tk

    (* Reply, Receive *)
    | Vis _ (Reply r) pk,
      Vis _ (| e ) tk =>
      match e in CoHTTPEvent T return (T -> _) -> _ with
      | Receive => fun tk => Tau (zipPS (pk tt) (tk r) n)
      | Send _ => fun _ => fail "zipPS: Reply/Send"
      end tk

    (* Ret *)
    | Ret v, _ => match v with end
    | _, Ret a => ret a
  end.

(* The specification acts as a collection of clients to the server. *)

Definition specEvent :=
  specE +' Common.stateE app_state +' CoHTTPEvent.
Definition atomicSpecEvent :=
  atomE specEvent.

(* This is one client. *)
(* TODO: smarter scheduling so the valid interleaving
   is found faster. *)
(* If we consider [trace] events to be invisible like [Tau],
   then the first and last [atomically] are not really
   necessary except for efficiency.
   The second one is important though, because we don't want
   two "threads" to race for the state. *)
Definition spec_client (r : req) : itree atomicSpecEvent unit :=
  n <- atomically (
      trace ("sending   " ++ show r);;
      send r);;
  expected_res <- atomically (
      s <- get;;
      put (execute r s);;
      ret (n, respond r s));;
  atomically (
    actual_res <- receive;;
    trace ("receiving " ++ show (snd actual_res));;
    if actual_res = expected_res ?
    then ret tt
    else fail "spec_client: unexpected response"
  ).

(* An "incorrect" version where we forgot to
   synchronize operations.
   It corresponds to a more relaxed consistency model
   than [spec_client].
   - it allows strictly more behaviors, (get/put interleaving)
     so it may miss bugs.
   - there are more possible interleavings to check,
     so it takes *much* longer to run.
   TODO: which of the incorrect servers does this accept?
 *)
Definition spec_client_nonatomic (r : req)
    : itree specEvent unit :=
  trace ("sending   " ++ show r);;
  n <- send r;;
  s <- get;;
  put (execute r s);;
  let expected_res := (n, respond r s) in
  actual_res <- receive;;
  trace ("receiving " ++ show (snd actual_res));;
  if actual_res = expected_res ?
  then ret tt
  else fail "spec_client_nonatomic".

(* The specification is just the interleaving of clients. *)
Fixpoint atomic_spec3 (arb_req : list req)
  : itree atomicSpecEvent unit :=
  match arb_req with
  | [] => ret tt
  | r :: arb_req' =>
    interleave (fun _ _ => tt)
               (spec_client r)
               (atomic_spec3 arb_req')
  end.

Definition spec3 (arb_req : list req) (s : app_state)
  : HTTPSpec unit :=
  eval_state (s : app_state)
           (hom (@fission _)
                (atomic_spec3 arb_req)).

Fixpoint atomic_spec3_nonatomic (arb_req : list req)
  : itree specEvent unit :=
  match arb_req with
  | [] => ret tt
  | r :: arb_req' =>
    interleave (fun _ _ => tt)
               (spec_client_nonatomic r)
               (atomic_spec3_nonatomic arb_req')
  end.

Definition spec3_nonatomic (arb_req : list req) (s : app_state)
  : HTTPSpec unit :=
    eval_state s (atomic_spec3_nonatomic arb_req).

End HTTPSERVERSPEC.

Module LINEARIZATON_EQUIVALENCE.

Export HTTPSERVERSPEC.
Import Setoid.
Set Bullet Behavior "Strict Subproofs".

CoInductive SpecImpM {E} {X} : relation (itree (specE +' E) X) :=
| SpecImpRet : forall x, SpecImpM (Ret x) (Ret x)
| SpecImpVis : forall Y (e : (specE +' E) Y) k1 k2,
    (forall y, SpecImpM (k1 y) (k2 y)) ->
    SpecImpM (Vis e k1) (Vis e k2)
| SpecImpTraceL : forall (msg : string) k1 m2,
    SpecImpM  (k1 tt) m2 ->
    SpecImpM (Vis (convert (Trace msg)) k1) m2
| SpecImpTraceR : forall (msg : string) m1 k2,
    SpecImpM m1 (k2 tt) ->
    SpecImpM m1 (Vis (convert (Trace msg)) k2)
| SpecImpOrL : forall k1 m2,
    SpecImpM (k1 true) m2 -> SpecImpM (k1 false) m2 ->
    SpecImpM (Vis Or_ k1) m2
| SpecImpFailL : forall k1 m2 s,
    SpecImpM (Vis (Fail_ s) k1) m2
| SpecImpOrR1 : forall k2 m1,
    SpecImpM m1 (k2 true) ->
    SpecImpM m1 (Vis Or_ k2)
| SpecImpOrR2 : forall k2 m1,
    SpecImpM m1 (k2 false) ->
    SpecImpM m1 (Vis Or_ k2)
| SpecImpOrDelay : forall m1 Z (e : (specE +' E) Z) k2 k2',
    (forall b, SpecImpM (k2 b) (Vis e (fun z : Z => k2' b z))) ->
    SpecImpM m1 (Vis e (fun z : Z => Vis Or_ (fun b => k2' b z))) ->
    SpecImpM m1 (Vis Or_ k2)
| SpecImpTauL : forall m1 m2,
    SpecImpM m1 m2 -> SpecImpM (Tau m1) m2
| SpecImpTauR : forall m1 m2,
    SpecImpM m1 m2 -> SpecImpM m1 (Tau m2).

(** This can be proved both inductively (over [xs])
    and coinductively, but the coinductive version (here)
    allows the [SpecImpM] hypothesis to contain corecursive
    calls in the context of a larger coinductive proof
    such as [spec_to_spec2]. *)
Lemma SpecImpM_pick_oneM_go:
  forall A E X (ys xs zs : list A) k (m : itree (specE +' E) X),
  (forall xs' x ys', zs = (xs' ++ x :: ys')%list -> SpecImpM (k (x, (xs' ++ ys')%list)) m) ->
  (ys ++ xs)%list = zs ->
  SpecImpM (bindM (pick_oneM_go ys xs) k) m.
Proof.
  intros; revert dependent ys; revert dependent xs.
  cofix go.
  intros.
  destruct xs; intros.
  * simpl.
    rewrite matchM.
    apply SpecImpFailL.
  * rewrite matchM.
    apply SpecImpOrL.
    - rewrite matchM.
      apply SpecImpTauL.
      apply H.
      congruence.
    - apply go.
      intros.
      rewrite <- app_assoc in *.
      assumption.
Defined.

Lemma SpecImpM_pick_oneM:
  forall A E X (xs : list A) k (m : itree (specE +' E) X),
  (forall xs' x ys', xs = (xs' ++ x :: ys')%list -> SpecImpM (k (x, (xs' ++ ys')%list)) m) ->
  SpecImpM (bindM (pick_oneM xs) k) m.
Proof.
  intros. apply SpecImpM_pick_oneM_go with (zs := xs). intros. auto. auto.
Defined.

(* TODO:
   From H find the state in the list states that we
   relate to here, and show that we relate to the corresponding
   entry in the new list of states. *)
Lemma next_enqueue pending s expected n r states :
  List.In (pending, s, expected)
          (flat_map next states) ->
  List.In (enqueue (n, r) (pending, s, expected))
          (flat_map next (map (enqueue (n, r)) states)).
Proof.
Admitted.

Lemma next_insert xs' ys' s expected n r states :
  List.In ((xs' ++ (n, r) :: ys')%list, s, expected)
          (flat_map next states) ->
  List.In ((xs' ++ ys')%list, execute r s,
           (n, respond r s) :: expected) (flat_map next states).
Proof.
Admitted.

Lemma dequeue_works pending s xs' ys' n r l :
  List.In (pending, s, (xs' ++ (n, r) :: ys')%list) l ->
  ~(flat_map (dequeue (n, r)) l = []).
Proof.
Admitted.

Lemma next_grows x l :
  List.In x l ->
  List.In x (flat_map next l).
Proof.
Admitted.

Lemma next_preserve_null s l :
  List.In ([], s, []) (flat_map next l) ->
  List.In ([], s, []) l.
Proof.
Admitted.

Lemma dequeue_next pending s xs' ys' n r states l :
        l = flat_map (dequeue (n, r)) (flat_map next states) ->
        ~(l = []) ->
        List.In (pending, s, (xs' ++ (n, r) :: ys')%list)
                (flat_map next states) ->
        List.In (pending, s, (xs' ++ ys')%list) l.
Proof.
Admitted.

Ltac stepL :=  match goal with [ |- SpecImpM ?m _ ] => rewrite (@matchM _ _ m) end.
Ltac stepR :=  match goal with [ |- SpecImpM _ ?m] => rewrite (@matchM _ _ m) end.

Theorem spec_to_spec2:
    forall
    (arb_req : list req)
    (pending_req : list (nat * req))
    (s : app_state)
    (expected_resp : list (nat * res))
    (states : list test_state )
    (H : List.In (pending_req, s, expected_resp) (flat_map next states)),
    SpecImpM (spec arb_req pending_req s expected_resp) (spec2 arb_req states).
Proof.
  cofix.
  intros.
  stepL.
  apply SpecImpOrL;
    [|apply SpecImpOrL;
      [|apply SpecImpOrL;
        [|apply SpecImpOrL;
          [|apply SpecImpFailL]]]].

  - (* spec1 is doing a send, so lets spec2 do the same *)
    stepR.
    apply SpecImpOrR2.
    destruct arb_req; [apply SpecImpFailL |]. (* arb_req <> [] *)
    (* - apply SpecImpVis; intro v; destruct v. *)
    stepL.
    apply SpecImpTraceL.
    stepL.
    apply SpecImpTauL.
    apply SpecImpOrR1.
    stepL. stepR. simpl.
    apply SpecImpVis. intro n.
    stepL. stepR.
    apply SpecImpTauL.
    apply SpecImpTauR.
    stepR.
    apply SpecImpTraceR.
    stepR.
    apply SpecImpTauR.
    apply spec_to_spec2.
    (* Precondition now *)
    apply next_enqueue; auto.

  - (* spec one picks a pending request and performs this *)
    (* Here, spec2 does _not_ do anything! *)
    apply SpecImpM_pick_oneM. intros.
    destruct x. simpl.
    apply spec_to_spec2.
    (* Precondition now: Relating execute and respond with next *)
    apply next_insert; rewrite <- H0; auto.

  - (* spec one picks delivers a response *)
    stepR.
    apply SpecImpOrR1.
    stepL. stepR.
    apply SpecImpVis. intro.
    stepL. stepR.
    apply SpecImpTauL.
    apply SpecImpTauR.
    stepL.
    apply SpecImpTraceL.
    stepL.
    apply SpecImpTauL.
    stepR.
    apply SpecImpTraceR.
    stepR.
    apply SpecImpTauR.
    apply SpecImpM_pick_oneM. intros.
    destruct y, x.
    destruct dec; [| apply SpecImpFailL]. (* dec = true *)
    inversion_clear e; subst.
    simpl.
    destruct (flat_map (dequeue (n0, r0)) (flat_map next states)) eqn:Heq.
    + (* We need to lead this to a contradiction: The set of next states is not empty *)
      exfalso.
      eapply dequeue_works; eauto.
    + apply spec_to_spec2 .
      (* Ok, back to a statement about relating state with state_list *)
      apply next_grows.
      eapply dequeue_next; eauto.
      intro; discriminate.

  - (* spec terminates: all requests have been responded to. *)
    stepR.
    do 2 apply SpecImpOrR2.
    apply SpecImpOrR1.
    destruct arb_req; [| apply SpecImpFailL]. (* arb_req = [] *)
    unfold spec_done; simpl.
    destruct (null pending_req && null expected_resp)%bool eqn:e;
      [| apply SpecImpFailL]. (* Both are empty. *)
    symmetry in e. apply andb_true_eq in e.
    replace pending_req with (@nil (nat * req)) in *
      by (destruct e as [e ?]; destruct pending_req;
          inversion e; auto).
    replace expected_resp with (@nil (nat * res)) in *
      by (destruct e as [? e]; destruct expected_resp;
          inversion e; auto).
    match goal with
    | [ |- SpecImpM _ (if ?c then _ else _) ] =>
      replace c with true
    end.
    + apply SpecImpRet.
    + symmetry. apply existsb_exists.
      eexists. split.
      * apply next_preserve_null.
        eauto.
      * reflexivity.
Abort.
(* Qed. *) (* This works but just takes so long to check. *)

Lemma anySpec_spec_delay :
  forall
    (arb_req : list req)
    (states : list test_state),
    SpecImpM
      (anySpec [
           anySpec (map (fun '(pending, s, expected) =>
             spec_send spec arb_req pending s expected) states);
           anySpec (map (fun '(pending, s, expected) =>
             spec_exec spec arb_req pending s expected) states);
           anySpec (map (fun '(pending, s, expected) =>
             spec_recv spec arb_req pending s expected) states)
      ])
      (anySpec (map (fun '(pending, s, expected) =>
                       spec arb_req pending s expected) states)).
Proof.
  intros.
  induction states as [ | s0 states].
  - repeat apply SpecImpOrL; apply SpecImpFailL.
  - admit.
Admitted.

Lemma SpecImpM_trans :
  forall E X (m n p : itree (specE +' E) X),
    SpecImpM m n -> SpecImpM n p -> SpecImpM m p.
Proof.
Admitted.

Lemma SpecImpM_anySpec_delay :
  forall E X1 X2 X3 Y Z
         (e : (specE +' E) Y)
         (f : X1 -> X2 -> X3 -> Y -> itree (specE +' E) Z)
         (xs : list (X1 * X2 * X3)),
    SpecImpM
      (Vis e (fun y => anySpec (map (fun '(x1,x2,x3) => f x1 x2 x3 y) xs)))
      (anySpec (map (fun '(x1,x2,x3) => Vis e (fun y => f x1 x2 x3 y)) xs)).
Proof.
Admitted.

Lemma map_matchM :
  forall E X Y Z T (f : X -> Y -> Z -> itree E T) (xs : list (X * Y * Z)),
    map (fun '(x, y, z) => f x y z) xs =
    map (fun '(x, y, z) => idM (f x y z)) xs.
Proof.
  induction xs.
  - auto.
  - simpl.
    apply f_equal2.
    destruct a as [[] ?].
    apply matchM.
    auto.
Qed.

Theorem spec2_to_spec:
    forall
    (arb_req : list req)
    (states : list test_state),
    SpecImpM
      (spec2 arb_req states)
      (anySpec (map (fun '(pending, s, expected) =>
                       spec arb_req pending s expected) states)).
Proof.
  cofix.
  intros.
  apply (fun p => SpecImpM_trans p (anySpec_spec_delay _ _)).
  stepL.
  apply SpecImpOrL.
  - (* Receive *)
    apply SpecImpOrR2.
    apply SpecImpOrR2.
    apply SpecImpOrR1.
    rewrite map_matchM with (f := spec_recv spec arb_req).
    stepL.
    simpl.
    apply (fun p => SpecImpM_trans p (SpecImpM_anySpec_delay _ _)).
    apply SpecImpVis.
    intros.
    (* This goal is becoming too big to follow. *)
Admitted.

Inductive labeled (E : Type -> Type) : Type :=
| Label : forall X, E X -> X -> labeled E.

Definition trace (E : Type -> Type) : Type := list (labeled E).

Inductive trace_of (E : Type -> Type) (X : Type)
  : trace E -> itree E X -> Prop :=
| TraceNil : forall x, trace_of [] (Ret x)
| TraceTau : forall t m, trace_of t m -> trace_of t (Tau m)
| TraceCons : forall Y (e : E Y) (y : Y) t k,
    trace_of t (k y) -> trace_of (Label e y :: t) (Vis e k).

Definition trace_inclusion E X
           (v : forall Y, E Y -> bool)
           (* Predicate for visible events. *)
           (m n : itree E X)
  := forall t,
    trace_of t m ->
    exists u,
      trace_of u m /\
      filter (fun '(Label Y e _) => v Y e) t =
      filter (fun '(Label Y e _) => v Y e) u.

Import ProofIrrelevance.

Definition visible : labeled (specE +' CoHTTPEvent) -> bool :=
  fun '(Label _ e _) =>
    match e with
    | (| Or ||) => false
    | (| Trace _ _ _ |||||) => false
    | _ => true
    end.

Ltac auto_clear :=
  repeat (match goal with
          | [ H : ?x = ?x |- _ ] => clear H
          end).

Ltac inj_pair2 :=
  repeat (match goal with
          | [ H2 : existT ?P ?T ?k1 = existT ?P ?T ?k2 |- _ ] =>
            apply inj_pair2 in H2
          end).

Lemma trace_event E X Y (e : E Y) y t (k : Y -> itree E X)
  : trace_of t (k y) -> trace_of (Label e y :: t) (Vis e k).
Proof.
  constructor; auto.
Qed.

Arguments trace_event {E X Y e} y.

Theorem spec2_to_spec_trace :
    forall
    (arb_req : list req)
    (states : list test_state)
    (t : trace _),
      trace_of t (spec2 arb_req states) ->
      exists pending s requested u,
        List.In (pending, s, requested) states /\
        trace_of u (spec arb_req pending s requested) /\
        filter visible t =
        filter visible u.

Proof.
  fix 3.
  intros arb_req states t Ht.

  (* or (recv; ...) (...) *)
  rewrite matchM in Ht; simpl in Ht.
  inversion Ht as [ | | bool1 e1 b1 t1 k1 Ht1 HL1 Hm1 ].
  clear Ht.
  subst.
  inj_pair2.
  subst.
  destruct b1.

  - (* recv; ... *)
    rewrite matchM in Ht1; simpl in Ht1.
    inversion Ht1 as [ | | Y2 e2 x2 t2 k2 Ht2 HL2 Hm2 ].
    clear Ht1.
    subst.
    inj_pair2.
    subst.

    (* tau; ... *)
    rewrite matchM in Ht2; simpl in Ht2.
    inversion Ht2 as [ | t2' m2' Ht2' | ].
    clear Ht2.
    subst.

    (* trace; ... *)
    rewrite matchM in Ht2'; simpl in Ht2'.
    inversion Ht2' as [ | | Y3 e3 x3 t3 k3 Ht3 HL3 Hm3 ].
    clear Ht2'.
    subst.
    inj_pair2.
    subst.
    simpl.

    (* tau; ... *)
    rewrite matchM in Ht3; simpl in Ht3.
    inversion Ht3 as [ | t3' m3' Ht3' | ].
    clear Ht3.
    subst.

    (* Recursive call *)
    remember (flat_map (dequeue x2) (flat_map next states)) as states2.
    destruct states2.
    inversion Ht3'.
    { subst. destruct y. } (* Failure events do not exist! *)
    apply spec2_to_spec_trace in Ht3'.
    destruct Ht3' as [pending [s [requested [u [ Hs [Hu Htu ]]]]]].

    do 4 eexists.
    split; [ | split].

    + admit.
    + rewrite matchM; simpl.
      apply (trace_event false). (* or *)
      apply (trace_event false). (* or *)
      apply (trace_event true).  (* or *)
      rewrite matchM; simpl.
      apply (trace_event x2).    (* recv *)
      rewrite matchM; simpl.
      constructor.               (* tau *)
      rewrite matchM; simpl.
      apply (trace_event tt).    (* trace *)
      rewrite matchM; simpl.
      constructor.               (* tau *)

Abort.

(*
Lemma
  : List.In s (flat_map (dequeue x) (flat_map next states)) ->
    exists s',
      List.In s' states /\
      s = dequeue x (next
*)

End LINEARIZATON_EQUIVALENCE.

(* ========================================================================= *)
(* Run some tests... *)

Import SPECMONAD.
Import HTTPSERVERSPEC.

Definition qc_test {X} `{Arbitrary X} `{Show X} (s: list X -> HTTPSpec unit) c : Checker :=
  let fuel := 40 in
  forAllShrink (resize 20 (listOf arbitrary))
               shrink
               (fun rs =>
                  collect (List.length rs)
                  (check_spec fuel (zipPS (c "SECRET")
                                         (s rs)
                                         0))).

Definition dummyspec :=
  qc_test (fun rs : list req => ret tt)
          server.

Definition qc_spec  :=
  qc_test (fun rs : list req => spec rs [] "SECRET" [])
          server.

Definition qc_spec2 :=
  qc_test (fun rs : list req => spec2 rs [([], "SECRET", [])])
          server.

Definition qc_spec3 :=
  qc_test (fun rs : list req => spec3 rs "SECRET")
          server.

Definition qc_spec3_nonatomic :=
  qc_test (fun rs : list req => spec3_nonatomic rs "SECRET")
          server.

(* Definition qc1 := qc_test (spec2 [([], "", [])]) server_delayed_wrong2. *)
(* QuickChick qc1. *)
Definition qc2 := qc_test (wrong_etag_spec [] "SECRET" []) server.
(*! QuickChick qc2. *)
Definition qc3 := (qc_test (wrong_etag_spec2 [([],"SECRET",[])] (fun _ => None) (fun _ => 0)) server).
(*! QuickChick qc3. *)

(* QuickChick qc_spec3. *)

Definition the_spec := qc_spec2.

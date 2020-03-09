From ITree Require Import ITree
     Interp.Traces
     Eq.Eq
     Events.State
.
From Paco Require Import paco.
Require GHC.Num.
Require GHC.Base.
Require Import Network.
Require Import Network_.
Require Import NetworkTypes.
Require Import Main.
Require Import IO.

Import ITree.Basics.Basics.Monads.

From ExtLib Require Import
     Structures.Monad.

From Coq Require Import
     Lists.List
     Strings.String.

(* Sanity check: Checking ITree representation of main. *)
Compute (burn 1 main).

(* Interpretation into the "world" state monad. *)
Eval cbn in (interp_io main).

Require Extraction.
(* One good thing about ITrees that it's executable.
   How do we recover this with axiomatized modules? *)
Extraction main.

(* =================== Nuggets from DeepWeb Server ==================== *)
(* ~~~ Notes ~~~
   Below is an experiment to define specification like the DeepWeb
   Server.

   Specifying programs using ITrees end up looking like writing
   functional programs with ITrees. The most interesting part was the
   "network refinement" relation, which uses trace semantics to reason
   about the refinement of a program. In the context of the IO monad,
   I think it would make most sense to intepret into the state monad
   instead. (State monad as a representation of """world""", as shown
   in IO.v)

   (Although in the context of concurrency, thinking about trace semantics
    *is* convenient.)
 *)

(* N.B.: These representations of "observerE" seems relevant
   for a low-level language like C. For Haskell, this doesn't seem
   terribly useful. (i.e. We can use `ioE` directly to give high-level
   specifications. `ioE` feels like it lives in a similar level of
   abstraction to the `specE` event types:

   https://github.com/DeepSpec/DeepWeb/blob/61a31786e2be7667afebcceaaac07c0e8aefa2c4/src/Free/Examples/SocketLoop.v

   where `specE` is based on `networkE` events:

   https://github.com/DeepSpec/DeepWeb/blob/ce9d9266d4f8d030934e30bc6d84533e9f56108b/src/MiniSwap/Lib/NetworkInterface.v

 *)


(* Meaningless attempt to define implE, since we don't end up using it. *)
Variant connection_id := Int.

(** Modeling implementation of server. *)

(* Server events. *)
Inductive observerE : Type -> Type :=
  (* observe a new connection. *)
| ObsConnect : observerE connection_id
(* receive a message from server. *)
| ObsFromServer : connection_id -> observerE (option string)
| ObsToServer : connection_id -> observerE string.

(** Failure and assertion.  *)
Inductive failureE : Type -> Type :=
| Fail : string -> failureE void.

Definition fail {E} `{failureE -< E} {X} (reason : string)
    : itree E X :=
    Vis (subevent _ (Fail reason)) (fun v : void => match v with end).

Definition assert_on {E A} `{failureE -< E}
           (r : string) (x : option A) (check: A -> bool) :
  itree E unit :=
  match x with
  | None => ret tt
  | Some a =>
    if check a then ret tt else fail ("Assertion failed." ++ r)
  end.

(* Observable interactions with server. *)
Definition obsConnect {E} `{observerE -< E} : itree E connection_id :=
  embed ObsConnect.

Definition obs_from_server {E} `{observerE -< E} :
  connection_id -> itree E (option string) :=
  embed ObsFromServer.

Import MonadNotation.
Local Open Scope monad.

Fixpoint msg_from_server {E} `{observerE -< E} `{failureE -< E}
         (c : connection_id) (m : string) : itree E unit :=
  ob <- obs_from_server c ;;
     assert_on "Message mismatch" ob (fun x => (x =? m)%string) ;;
     ret tt
.

(* The server monad we write implementations in.
   A server is a program with external network effects. *)
Definition implE := observerE +' failureE.

(* Behavior of implementation model is denoted as the traces of a program. *)
Definition impl_behavior (impl: itree implE unit) : trace -> Prop :=
  fun tr => is_trace impl tr.

(* ====================================================== *)
(** *Modeling specification of server *)

(* This is not useful for this "non-concurrent" server. *)

(* Network refinement is the refinement of the trace semantics between the
   implementation and specification model. *)

Definition specE := ioE.

Definition spec_behavior (spec: itree ioE unit) : trace -> Prop :=
  fun tr => is_trace spec tr.

(* N.B.: Network refinement and linearization in this instance of the
   server is not applicable, because we don't care about concurrent connections
   just yet. *)
(* Definition specE := serverE +' failureE. *)

(* implE and specE are the same in our model. *)
(*
Definition network_refines impl spec : Prop :=
  forall tr,
    impl_behavior impl tr -> spec_behavior spec tr. *)

(* CoFixpoint linear_spec (conn : connection_id) (s : string) : itree specE unit :=
  c <- connect;;
    Tau (linear_spec c s).

 Theorem server_correct:
  exists (impl_model : itree serverE unit),
    network_refines (linear_spec app).
*)

Theorem runConn_terminates:
  forall s, not (divergence (runConn s)).
Proof.
  intro.
  intro. inversion H. inversion paco_observe. inversion SIM.
  destruct s. Admitted.

(* Network.socket NetworkTypes.AF_INET NetworkTypes.Stream #0 GHC.Base.>>=
  (fun sock =>
     Network.setSocketOption sock NetworkTypes.ReuseAddr #1 GHC.Base.>>
     (Network.bind sock (NetworkTypes.SockAddrInet #4242 NetworkTypes.iNADDR_ANY)
      GHC.Base.>>
      (Network.listen sock #2 GHC.Base.>> mainLoop sock))). *)

Definition runConn_spec : Socket * SockAddr -> itree specE unit :=
  fun '(sock, _) => send sock (GHC.Base.hs_string__ "Hello World!");;
   close sock
.

Theorem runConn_correct:
  forall s, runConn s ≈ runConn_spec s.
Proof.
  unfold runConn_spec, runConn. cbn. intros.
  destruct s. reflexivity.
Qed.

(* world = (server * client * sockets * messages)
   server = (list Socket * nat * bool)
   client = Base.String
   sockets = list Socket
   messages = list (Socket * Base.String)
 *)

Section invariants.

  Context {E : Type -> Type}.
  Inductive world_invariant : stateT world (itree E) unit -> Prop :=.

  Theorem runConn_preserves_world_invariant:
  forall s,
    world_invariant (interp_io (runConn s)).
  Proof.
  Admitted.

End invariants.

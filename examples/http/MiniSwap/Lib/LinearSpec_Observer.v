(* Effects for specifications *)

(* Our specifications are itrees whose effects allow them to
   _observe_ events and make assertions to define what makes a
   valid interaction.
 *)

(* If you come from [Lib.LinearSpec] the types here will look
   different from those over there.
   The functions below are actually more polymorphic, so that
   they can be used with different effect types.
   You actually use the functions below when you import
   [Lib.LinearSpec]; the module types with simpler signatures
   are only for the sake of exposition.

   This is also the case for [Lib.LinearSpec_Server].
 *)

Generalizable Variable E.
Typeclasses eauto := 6.

From QuickChick Require Import QuickChick.

Require Import List.
Require Import PArith.
Require Fin.
Import ListNotations.

From Custom Require Import Show String.

Require Import DeepWeb.Free.Monad.Free.
Import MonadNotations.
Require Import DeepWeb.Free.Monad.Common.

Import SumNotations.

Require Import DeepWeb.Lib.Util.

Require Import DeepWeb.Lib.LinearSpec_Traces.

(* begin hide *)
Set Warnings "-extraction-opaque-accessed,-extraction".
(* end hide *)

Module Export ObserverType.
(** The type of observations that can be made by the spec. *)
Inductive observerE : Type -> Type :=
| (* Observe the creation of a new connection *)
  ObsConnect : observerE connection_id

| (* Observe a byte going into the server on a particular
     connection *)
  ObsToServer : connection_id -> observerE byte

  (* Observe a byte going out of the server.  This action can return
     [None], indicating a "hole" as a way to hypothesize that the
     server sent some message we haven't yet received, so we can keep
     testing the rest of the trace. *)
| ObsFromServer : connection_id -> observerE (option byte).

(* The [ObsFromServer] effect returns an [option].
   [None] is a "hole" in the observed trace, it represents a
   message hypothetically sent by the server and that we haven't
   yet received. These holes allow us to keep exploring an
   observer even in the presence of partial outputs from the
   server. *)

(* Note: The spec writer must be careful that, if a trace with
   holes is rejected, then it must also be for any substitution
   of actual values for those holes. *)
End ObserverType.

(* The event type we write specifications over. *)
Definition specE := failureE +' nondetE +' observerE.

Definition obs_connect {E} `{observerE -< E} : itree E connection_id :=
  embed ObsConnect.

Definition obs_to_server {E} `{observerE -< E} :
  connection_id -> itree E byte :=
  embed ObsToServer.

Definition obs_from_server {E} `{observerE -< E} :
  connection_id -> itree E (option byte) :=
  embed ObsFromServer.

(* Make an assertion on a value, if it exists. *)
Definition assert_on {E A} `{failureE -< E} `{nondetE -< E}
           (r : string) (oa : option A) (check : A -> bool) :
  itree E unit :=
  match oa with
  | None => ret tt
  | Some a =>
    if check a then ret tt else fail ("assertion failed: " ++ r)
  end.

(* Observe a message of length [n] sent to the server. *)
Fixpoint obs_msg_to_server `{observerE -< E}
         (n : nat) (c : connection_id) : itree E bytes :=
  match n with
  | O => ret ""
  | S n =>
    b <- obs_to_server c;;
    bs <- obs_msg_to_server n c;;
    ret (b ::: bs)
  end%string.

(* Observe a message of length [n] received from the server. *)
Fixpoint obs_msg_from_server
         `{observerE -< E} `{failureE -< E} `{nondetE -< E}
         (c : connection_id) (msg : bytes) :
  itree E unit :=
  match msg with
  | "" => ret tt
  | b0 ::: msg =>
    ob <- obs_from_server c;;
    assert_on "bytes must match" ob (fun b1 => b1 = b0 ?);;
    obs_msg_from_server c msg
  end%string.

(* A [hypo_event] is an [observerE] effect ([observerE X])
   together with its result ([X]) *)
Definition to_observerE_event (e : hypo_event) :
  Traces.event observerE :=
  match e with
  | NewConnection c => Traces.Event ObsConnect c
  | ToServer c b => Traces.Event (ObsToServer c) b
  | FromServer c ob => Traces.Event (ObsFromServer c) ob
  end.

Definition to_observerE_trace : hypo_trace -> Traces.trace observerE :=
  List.map to_observerE_event.

(* [is_spec_trace observer tr] holds if [tr] is a trace of
   the [observer]; [tr] may contain holes. *)
Definition is_spec_trace : itree specE unit -> hypo_trace -> Prop :=
  fun observer tr => Traces.is_trace' observer (to_observerE_trace tr).

(* The observable behavior of a spec. *)
Definition spec_behavior (spec : itree specE unit)
  : real_trace -> Prop :=
  fun tr => exists tr_spec : real_trace,
      is_spec_trace spec tr_spec /\
      network_reordered tr_spec tr.

(**)

(* Equality comparison, return a proof of equality of the
   indices (this could be generalized to a complete decision
   procedure). *)
Definition observer_eq {X Y : Type}
           (e1 : observerE X) (e2 : observerE Y) :
  option (X = Y) :=
  match e1, e2 with
  | ObsConnect, ObsConnect => Some eq_refl
  | ObsToServer c, ObsToServer c'
  | ObsFromServer c, ObsFromServer c' =>
    if c = c' ? then Some eq_refl else None
  | _, _ => None
  end.

Definition coerce {X Y : Type} (p : X = Y) (x : X) : Y :=
  match p in eq _ Y return Y with
  | eq_refl => x
  end.

(* The spec can be viewed as a set of traces. *)

(* An [event] is an observer action together with its result. *)

Definition match_obs {X Y R S : Type}
           (e0 : observerE X)
           (e1 : observerE Y)
           (cont : S -> R)
           (fail_ : R) :
  X -> (Y -> S) -> R :=
  match e0 in observerE X, e1 in observerE Y
        return X -> (Y -> _) -> _ with
  | ObsConnect, ObsConnect => fun x k => cont (k x)
  | ObsToServer c, ObsToServer c' => fun x k =>
    if c = c' ? then
      cont (k x)
    else
      fail_
  | ObsFromServer c, ObsFromServer c' => fun x k =>
    if c = c' ? then
      cont (k x)
    else
      fail_
  | _, _ => fun _ _ => fail_
  end.

(* [exists x, k x = true] *)
Definition nondet_exists {X : Type}
           (e : nondetE X) (k : X -> simple_result) : simple_result :=
  match e in nondetE X' return (X' -> X) -> _ with
  | Or => fun id =>
    (k (id false) || k (id true))%result
  end (fun x => x).

(* Basically, a trace [t] belongs to a tree if there is a path
   through the tree (a list of [E0] effects) such that its
   restriction to [observerE] events is [t].
   Because trees are coinductive (in particular, they can contain
   arbitrary sequences of [Tau] or [Vis] with invisible effects),
   it is not possible to decide whether a trace matches the tree.
   Thus we add a [fuel] parameter assumed to be "big enough"
   for the result to be reliable. *)

Fixpoint is_spec_trace_test_
         (max_depth : nat) (s : itree specE unit) (t : hypo_trace) :
  simple_result :=
  match max_depth with
  | O => DONTKNOW
  | S max_depth =>
    match s, t with
    | Tau s, t => is_spec_trace_test_ max_depth s t
    | Ret tt, [] => OK tt
    | Ret tt, _ :: _ => FAIL tt
    | Vis (| e1 ) k, x :: t =>
      match to_observerE_event x with
      | Traces.Event e0 y =>
        match_obs e0 e1 (fun s => is_spec_trace_test_ max_depth s t)
                  (FAIL tt) y k
      end
    | Vis (| e1 ) k, [] => OK tt
    (* The trace belongs to the tree [s] *)
    | Vis (| _Or |) k, t =>
      nondet_exists _Or (fun b => is_spec_trace_test_ max_depth (k b) t)
    | Vis ( _Fail ||) _, _ => FAIL tt
    end
  end.

(* It seems we can set the max depth as high as possible,
   at least for the spec we have now. *)
Definition is_spec_trace_test :
  itree specE unit -> hypo_trace -> simple_result :=
  is_spec_trace_test_ _1000.

(* The traces produced by the tree [swap_observer] are very structured,
   with sequences of bytes sent and received alternating tidily.
   However, in general:
   - the network may reorder some messages, so the traces we
     actually see during testing will not be directly checkable
     using [is_spec_trace_test], they must be reordered first;
   - a server implementation may also want to reorder responses
     differently for performance and other practical reasons
     (e.g., avoiding "head-of-line blocking");
     here we will consider a server correct if it cannot be
     distinguished over the network from a server that actually
     produces the same traces as the observer above. *)

(* The network's behavior is defined in [Lib.LinearSpec_Traces]
   and is accounted for in testing in [Lib.LinearSpec_Descramble]. *)

From ITree Require Import
     ITree
     Events.Nondeterminism
     Events.Exception
     Subevent.

From Coq Require Import
     Ascii String List PArith ZArith.
From Coq Require Fin.

From QuickChick Require Import QuickChick.
Open Scope monad_scope.
Require Import ServerDefs StringLib.
From ExtLib Require Import Monad.
Import ListNotations MonadNotation.

Section SpecEffects.

  Generalizable Variable E.

(* ====================================================== *)
(** *Specification Effects *)
(* ====================================================== *)

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

Definition failureE := exceptE string.

Definition fail `{failureE -< E} {R} (reason : string) : itree E R
  := vis (Throw reason) (fun v : void => match v with end).

(* This can fail if the list is empty. *)
Definition choose {E} `{failureE -< E} `{nondetE -< E} {X}
  : list X -> itree E X := fix choose' xs : itree E X :=
  match xs with
  | [] => fail "choose: No choice left"
  | x :: xs =>
    or (Ret x) (choose' xs)
  end.

(* Definition fail (err : string) := trigger (Throw err) *)
Definition specE := nondetE +' observerE +' failureE.

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
    (assert_on "bytes must match" ob (fun b1 => (b1 = b0 ?)));;
    obs_msg_from_server c msg
  end%string.

End SpecEffects.

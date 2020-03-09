Set Printing Universes.

Require Import String List.
Import ListNotations.

From ITree Require Export ITree.

From ExtLib Require Import Structures.Monad.

From ExtLib Require Export Structures.Monad.

Import ITreeNotations.
Open Scope itree.

(* Bytes *)

(* We use Coq's standard [string] type to use its
   pretty-printing niceness. *)

(* Single byte *)
Definition byte : Type := Ascii.ascii.

(* Bytestring *)
Definition bytes : Type := String.string.

Bind Scope string_scope with bytes.

Fixpoint replicate_bytes {E} (n : nat) (get_byte : itree E byte) :
  itree E bytes :=
  match n with
  | O => ret ""
  | S n =>
    b <- get_byte;;
    bs <- replicate_bytes n get_byte;;
    ret (String b bs)
  end%string.

(* Loop over each byte. *)
Fixpoint for_bytes {E} (bs : bytes) (eat_byte : byte -> itree E unit) :
  itree E unit :=
  match bs with
  | "" => ret tt
  | String b bs => eat_byte b;; for_bytes bs eat_byte
  end%string.

(* ew... bytes = string *)
Fixpoint list_of_bytes (bs : bytes) : list byte :=
  match bs with
  | EmptyString => nil
  | String c s => c :: list_of_bytes s
  end.

Lemma app_list_of_bytes bs1 bs2 :
  list_of_bytes (bs1 ++ bs2) = list_of_bytes bs1 ++ list_of_bytes bs2.
Proof.
  induction bs1 as [| b bs1' IH].
  - reflexivity.
  - simpl. rewrite IH. reflexivity.
Qed.

Lemma length_list_of_bytes bs :
  length (list_of_bytes bs) = String.length bs.
Proof.
  induction bs as [|b bs' IH].
  - reflexivity.
  - simpl. rewrite IH. reflexivity.
Qed.

Lemma list_of_substring : forall n m s,
    list_of_bytes (substring n m s) =
    firstn m (skipn n (list_of_bytes s)).
Proof.
  induction n as [| n IH]; intros m s.
  - simpl.
    generalize dependent s.
    induction m as [| m IH]; intros []; simpl; auto.
    rewrite IH.
    auto.
  - destruct s; simpl; auto.
    destruct m; auto.
Qed.

From Custom Require Import
     Monad String List.
Import MonadNotations.

From QuickChick Require Import
     Decidability Show.

From DeepWeb.Free Require Import
     Monad.Free.

(* Bytes *)

(* We use Coq's standard [string] type to use its
   pretty-printing niceness. *)

(* Single byte *)
Definition byte : Type := Ascii.ascii.

(* Bytestring *)
Definition bytes : Type := String.string.

Bind Scope string_scope with bytes.

(* Iterate a byte-producing process [n] times. *)
Fixpoint replicate_bytes {E} (n : nat) (get_byte : itree E byte) :
  itree E bytes :=
  match n with
  | O => ret ""
  | S n =>
    b <- get_byte;;
    bs <- replicate_bytes n get_byte;;
    ret (b ::: bs)
  end%string.

(* Loop over each byte. *)
Fixpoint for_bytes {E} (bs : bytes) (eat_byte : byte -> itree E unit) :
  itree E unit :=
  match bs with
  | "" => ret tt
  | b ::: bs => eat_byte b;; for_bytes bs eat_byte
  end%string.

(* Get a null-terminated sequence of bytes, excluding the zero-byte
   delimiter. Loops infinitely if there is no zero-byte. *)
Definition get_str {E} (get_byte : itree E byte) : itree E bytes :=
  (cofix get_str' (mk_bytes : bytes -> bytes) : itree E bytes :=
     bind_itree get_byte (fun b =>
     if b = "000"%char ? then
       ret (mk_bytes "")%string
     else
       Tau (get_str' (fun bs => mk_bytes (b ::: bs)%string))))
    (fun bs => bs).

(* Loop over each byte and an extra null byte at the end. *)
Fixpoint for_str {E} (bs : bytes) (eat_byte : byte -> itree E unit) :
  itree E unit :=
  match bs with
  | "" => eat_byte "000"%char
  | b ::: bs => eat_byte b;; for_str bs eat_byte
  end%string.

(* ew... bytes = string *)
Fixpoint list_of_bytes (bs : bytes) : list byte :=
  match bs with
  | EmptyString => []
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

(* Network *)

Require Import ZArith.

Inductive connection_id : Type := Connection (c : nat).

Definition eqb_connection_id :
  forall c1 c2 : connection_id, {c1 = c2} + {c1 <> c2}.
Proof. intros [] []; dec_eq. Defined.

Instance Eq_connection_id : Dec_Eq connection_id :=
  { dec_eq := eqb_connection_id }.

Instance Show_connection_id : Show connection_id :=
  { show := fun '(Connection c) => show c }.

Instance show_unit : Show unit :=
  { show _ := "tt"%string }.

(* Testing *)

(* Partial test result type. *)

Inductive result (W CE : Type) :=
| OK (witness : W)       (* Success, with a witness *)
| FAIL (counterex : CE)  (* Failure, with a counterexample *)
| DONTKNOW               (* Test ran out of fuel or something *)
.

Arguments OK {W} {CE}.
Arguments FAIL {W} {CE}.
Arguments DONTKNOW {W} {CE}.

(* A result with no meaningful witnesses of success or
   counterexamples. *)
Definition simple_result := result unit unit.

(* We restrict this to [unit] counterexamples to
   avoid losing information accidentally. *)
Definition or_result {W : Type} :
  result W unit -> (unit -> result W unit) -> result W unit :=
  fun r1 r2 =>
    match r1 with
    | OK w => OK w
    | FAIL tt | DONTKNOW => r2 tt
    end.

Notation "x || y" := (or_result x (fun _ => y)) : result_scope.

Delimit Scope result_scope with result.

From QuickChick Require QuickChick.

Section CheckableResult.
Import QuickChick.

Definition collectResult {A CE} (r : result A CE) : string :=
  match r with
  | OK _    => "Found"
  | FAIL _ => "Not Found"
  | DONTKNOW  => "Out of Fuel"
  end.

Global Instance Checkable_result {A CE : Type} `{Show A} `{Show CE}
  : Checkable (@result A CE)  :=
  {| checker r :=
       collect (collectResult r)
       match r with
       | OK _ => checker true
       | FAIL _ => checker false
       | DONTKNOW => checker tt
       end |}.

End CheckableResult.

(* Option type *)

Definition or_option {A : Type} :
  option A -> (unit -> option A) -> option A :=
  fun r1 r2 =>
    match r1 with
    | None => r2 tt
    | Some a => Some a
    end.

Notation "x <|> y" := (or_option x (fun _ => y))
(at level 30) : option_scope.

Delimit Scope option_scope with option.

(* Trick extraction for big numbers. *)
Definition _10 : nat := 5 * 2.
Definition _100 : nat := _10 * _10.
Definition _1000 : nat := _100 * _10.

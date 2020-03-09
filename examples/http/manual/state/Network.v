Generalizable Variable E.
Typeclasses eauto := 6.


From Coq Require Import List ZArith String.

Require Import Util ITreePrelude.

Import ListNotations.

(* begin hide *)
Set Warnings "-extraction-opaque-accessed,-extraction".
(* end hide *)

Module Export Network.

Variant connection_id : Type := Connection (c : nat).

Definition eqb_connection_id :
  forall c1 c2 : connection_id, {c1 = c2} + {c1 <> c2}.
Proof.
  intros [] [].
  destruct (c =? c0) eqn:H; auto.
  - apply beq_nat_true in H.
    subst; auto.
  - apply beq_nat_false in H.
    right.
    unfold not; intros conn_eq; inversion conn_eq; contradiction.
Defined.

Record endpoint_id : Type := Endpoint
  { port_number : Z;
  }.

(* Dummy value for the endpoint (ignored). *)
Definition dummy_endpoint : endpoint_id
  := Endpoint 0.

Variant networkE : Type -> Type :=
| Listen : endpoint_id -> networkE unit
| Accept : endpoint_id -> networkE connection_id
| Shutdown : connection_id -> networkE unit
| RecvByte : connection_id -> networkE byte
| SendByte : connection_id -> byte -> networkE unit.
  
Definition listen `{networkE -< E}
  : endpoint_id -> itree E unit := embed Listen.

Definition accept `{networkE -< E}
  : endpoint_id -> itree E connection_id := embed Accept.

Definition shutdown `{networkE -< E}
  : connection_id -> itree E unit := embed Shutdown.

Definition recv_byte `{networkE -< E}
  : connection_id -> itree E byte := embed RecvByte.

Definition send_byte `{networkE -< E}
  : connection_id -> byte -> itree E unit := embed SendByte.

(* Helper for [recv]. *)
Fixpoint recv' `{networkE -< E} `{nondetE -< E}
         (c : connection_id) (len : nat) : itree E bytes :=
  (match len with
  | O => ret ""
  | S len =>
    b <- recv_byte c ;;
    or (ret (String b ""))
       (bs <- recv' c len ;;
        ret (String b bs))
  end)%string.

(* Receive a string of length at most [len].
   The return value [None] signals that a connection was closed,
   when modelling the [recv()] POSIX syscall. *)
Definition recv `{networkE -< E} `{nondetE -< E}
           (c : connection_id) (len : nat) : itree E (option bytes) :=
  or (ret None)
     (bs <- recv' c len;;
      ret (Some bs)).

(* Receive a string of length [len] exactly. *)
Definition recv_full `{networkE -< E}
           (c : connection_id) (len : nat) : itree E bytes :=
  replicate_bytes len (recv_byte c).

Fixpoint send `{networkE -< E} `{nondetE -< E}
         (c : connection_id) (bs : bytes) : itree E nat :=
  match bs with
  | EmptyString => ret 0
  | String b bs =>
    or (ret 0)
       (send_byte c b ;; n <- send c bs ;; ret (S n))
  end.

(* Send all bytes in a bytestring. *)
Definition send_full `{networkE -< E}
           (c : connection_id) (bs : bytes) : itree E unit :=
  for_bytes bs (send_byte c).

(* All numbers between 0 and [n-1] included. *)
Fixpoint range (n : nat) : list nat :=
    match n with
    | O => []
    | S n' => range n' ++ [n']
    end.

Lemma in_range: forall n k, In k (range n) -> 0 <= k < n.
Proof.
  induction n; intros k; simpl; intros H; [contradiction |].
  apply in_app_or in H.
  destruct H.
  - apply IHn in H.
    omega.
  - simpl in H; destruct H; omega + contradiction.
Qed.

End Network.


(* Effects for server implementations *)

(* If you come from [LinearSpec] the types here will look
   different from those over there.
   The functions below are actually more polymorphic, so that
   they can be used with different effect types.
   You actually use the functions below when you import
   [LinearSpec]; the module types with simpler signatures
   are only for the sake of exposition.

   This is also the case for [LinearSpec_Observer].
 *)

From Custom Require Import String.

Require Import DeepWeb.Free.Monad.Free.
Require Import DeepWeb.Free.Monad.Common.
Import SumNotations.
Import MonadNotations.

Require Import DeepWeb.Lib.Util.
Require Import DeepWeb.Lib.LinearSpec_Traces.

Module LinearSpec_Server.

Module Export ServerType.
(* A simple interface of server effects. *)
Inductive serverE : Type -> Type :=
| Accept   : serverE connection_id
| RecvByte : connection_id -> serverE byte
| SendByte : connection_id -> byte -> serverE unit
.
End ServerType.

(* The server monad we write implementations in.
   A server is a program with internal nondeterminism and
   external network effects. *)
Definition implE := failureE +' nondetE +' serverE.

(* Accept a new connection. *)
Definition accept {E} `{serverE -< E}
  : itree E connection_id := embed Accept.

(* Receive one byte from a connection. *)
Definition recv_byte {E} `{serverE -< E}
  : connection_id -> itree E byte := embed RecvByte.

(* Send one byte to a connection. *)
Definition send_byte {E} `{serverE -< E}
  : connection_id -> byte -> itree E unit := embed SendByte.

(* Receive up to [n] bytes. *)
Fixpoint recv {E} `{serverE -< E} `{nondetE -< E}
           (c : connection_id) (n : nat) : itree E bytes :=
  match n with
  | O => ret ""
  | S n =>
    b <- recv_byte c;;
    bs <- recv c n;;
    ret (b ::: bs)
  end%string.

(* Receive a bytestring of length [n] exactly. *)
Definition recv_full {E} `{serverE -< E}
           (c : connection_id) (n : nat) : itree E bytes :=
  replicate_bytes n (recv_byte c).

(* Send all bytes in a bytestring. *)
Definition send {E} `{serverE -< E}
         (c : connection_id) (bs : bytes) : itree E unit :=
  for_bytes bs (send_byte c).

(* A [real_event] is a [serverE] effect ([serverE X])
   together with its result ([X]) *)
Definition to_serverE_event (ev : real_event) :
  Traces.event serverE :=
  match ev with
  | NewConnection c => Traces.Event Accept c
  | ToServer c b => Traces.Event (RecvByte c) b
  | FromServer c b => Traces.Event (SendByte c b) tt
  end.

Definition from_serverE_event (ev : Traces.event serverE) :
  real_event :=
  match ev with
  | Traces.Event Accept c => NewConnection c
  | Traces.Event (RecvByte c) b => ToServer c b
  | Traces.Event (SendByte c b) _ => FromServer c b
  end.

Lemma to_from_serverE_event ev :
  from_serverE_event (to_serverE_event ev) = ev.
Proof.
  destruct ev; auto.
Qed.

Lemma from_to_serverE_event ev :
  to_serverE_event (from_serverE_event ev) = ev.
Proof.
  destruct ev as [? [] x]; auto; destruct x; auto.
Qed.

Definition to_serverE_trace : real_trace -> Traces.trace serverE :=
  List.map to_serverE_event.

Definition from_serverE_trace : Traces.trace serverE -> real_trace :=
  List.map from_serverE_event.

Lemma from_to_serverE_trace tr :
  to_serverE_trace (from_serverE_trace tr) = tr.
Proof.
  induction tr.
  + reflexivity.
  + simpl; rewrite from_to_serverE_event; f_equal; auto.
Qed.

Lemma to_from_serverE_trace tr :
  from_serverE_trace (to_serverE_trace tr) = tr.
Proof.
  induction tr.
  + reflexivity.
  + simpl; rewrite to_from_serverE_event; f_equal; auto.
Qed.

Lemma roundtrip_serverE_trace tr tr' :
  tr' = to_serverE_trace tr <-> from_serverE_trace tr' = tr.
Proof.
  split; intros; subst.
  - rewrite to_from_serverE_trace; auto.
  - rewrite from_to_serverE_trace; auto.
Qed.

(* [is_impl_trace server tr] holds if [tr] is a trace of the [server]. *)
Definition is_impl_trace : itree implE unit -> real_trace -> Prop :=
  fun server tr => Traces.is_trace' server (to_serverE_trace tr).

Definition impl_behavior (impl : itree implE unit)
  : real_trace -> Prop :=
  fun tr => exists tr_impl : real_trace,
      is_impl_trace impl tr_impl /\
      network_reordered tr_impl tr.

End LinearSpec_Server.

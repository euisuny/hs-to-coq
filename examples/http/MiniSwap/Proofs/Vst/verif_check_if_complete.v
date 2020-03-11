Require Import String.

Require Import DeepWeb.Spec.Swap_ImplModel.

From DeepWeb.Spec.Vst
     Require Import MainInit Gprog check_if_complete_spec.

From DeepWeb.Lib
     Require Import VstLib.

From DeepWeb.Proofs.Vst
     Require Import VerifLib.

Set Bullet Behavior "Strict Subproofs".

Lemma Z_nat_bij : forall a b, Z.of_nat a = b -> a = Z.to_nat b.
Proof.
  intros; subst; rewrite Nat2Z.id; reflexivity.
Qed.

Lemma nat_Z_bij : forall a b, 0 <= b -> Z.to_nat b = a -> b = Z.of_nat a.
Proof.
  intros; subst; rewrite Z2Nat.id; auto.
Qed.

Lemma body_check_if_complete:
  semax_body Vprog Gprog f_check_if_complete
             (check_if_complete_spec BUFFER_SIZE).
Proof.
  start_function.

  forward_if.
  {
    forward.
    Exists 1.
    entailer!.

    unfold is_complete.
    rewrite Nat.eqb_eq.
    autorewrite_sublist.
    unfold BUFFER_SIZE.
    rewrite Zlength_val_string_len in H2.
    apply Z_nat_bij in H2; assumption.
  } 

  forward.

  Exists 0.
  entailer!.
  unfold is_complete.
  rewrite <- not_true_iff_false.
  unfold not, BUFFER_SIZE; intros Hsize.
  apply H0.
  revert Hsize.
  autorewrite_sublist.
  rewrite Nat.eqb_eq.
  intros.
  rewrite Zlength_val_string_len.
  apply nat_Z_bij; auto. omega.
Qed.  

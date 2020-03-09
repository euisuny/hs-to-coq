Require Import Coq.PArith.BinPos Coq.ZArith.BinInt.

Lemma Decimal_revapp_not_nil (d1 d2 : Decimal.uint):
  d2 <> Decimal.Nil ->
  Decimal.revapp d1 d2 <> Decimal.Nil.
Proof.
  revert d2; induction d1; intros d2 Hd2; intros H; simpl in H;
    try solve [
          match type of H with
          | context[Decimal.revapp _ ?d2] =>
            unfold not in IHd1; apply IHd1 with d2; eauto;
            intro; discriminate
          end
        ].
  contradiction.
Qed.

Lemma Decimal_uint_decidable (x y : Decimal.uint): {x = y} + {x <> y}.
Proof.
  revert y.
  induction x; intros y; destruct y;
    try solve [left; auto]; try solve [right; intro; discriminate];
      solve [destruct (IHx y);
             [subst; auto
             | right; intro Hcontra; inversion Hcontra; contradiction]
            ].
Qed.

Lemma Decimal_revapp_nil_inv (d1 d2 : Decimal.uint):
  Decimal.revapp d1 d2 = Decimal.Nil -> d1 = Decimal.Nil /\ d2 = Decimal.Nil.
Proof.
  intros H.
  destruct (Decimal_uint_decidable d2 Decimal.Nil).
  { subst d2.
    split; auto.
    destruct d1; simpl in H; auto;
      apply Decimal_revapp_not_nil in H; try contradiction;
        intro Hcontra; discriminate.
  }
  apply Decimal_revapp_not_nil in H; try contradiction; trivial.
Qed.

Lemma Decimal_revapp_nil_iff (d1 d2 : Decimal.uint):
  Decimal.revapp d1 d2 = Decimal.Nil <-> d1 = Decimal.Nil /\ d2 = Decimal.Nil.
Proof.
  split; intros H.
  - apply Decimal_revapp_nil_inv in H; trivial.
  - destruct H; subst d1 d2; auto.
Qed.

Lemma Decimal_rev_nil (d : Decimal.uint):
  Decimal.rev d = Decimal.Nil <-> d = Decimal.Nil.
Proof.
  unfold Decimal.rev.
  split; intro H;
    [ rewrite Decimal_revapp_nil_iff in H; tauto |].
  subst d.
  reflexivity.
Qed.

Lemma Decimal_revapp_ind (P : Decimal.uint -> Decimal.uint -> Prop)
      (d1 d2 : Decimal.uint) :
  P d1 d2 ->
  (forall d1 d2, P (Decimal.D0 d1) d2 -> P d1 (Decimal.D0 d2)) ->
  (forall d1 d2, P (Decimal.D1 d1) d2 -> P d1 (Decimal.D1 d2)) ->
  (forall d1 d2, P (Decimal.D2 d1) d2 -> P d1 (Decimal.D2 d2)) ->
  (forall d1 d2, P (Decimal.D3 d1) d2 -> P d1 (Decimal.D3 d2)) ->
  (forall d1 d2, P (Decimal.D4 d1) d2 -> P d1 (Decimal.D4 d2)) ->
  (forall d1 d2, P (Decimal.D5 d1) d2 -> P d1 (Decimal.D5 d2)) ->
  (forall d1 d2, P (Decimal.D6 d1) d2 -> P d1 (Decimal.D6 d2)) ->
  (forall d1 d2, P (Decimal.D7 d1) d2 -> P d1 (Decimal.D7 d2)) ->
  (forall d1 d2, P (Decimal.D8 d1) d2 -> P d1 (Decimal.D8 d2)) ->
  (forall d1 d2, P (Decimal.D9 d1) d2 -> P d1 (Decimal.D9 d2)) ->
  P (Decimal.Nil) (Decimal.revapp d1 d2).
Proof.
  revert d2; induction d1; intros d2; intros Hbase Hind; simpl; auto;
    apply IHd1; auto.
Qed.

Lemma Decimal_rev_involutive (d : Decimal.uint):
  Decimal.rev (Decimal.rev d) = d.
Proof.
  unfold Decimal.rev at 1.
  set (P d1 d2 := Decimal.revapp d2 d1 = d).
  change (P Decimal.Nil (Decimal.rev d)).
  unfold Decimal.rev.
  apply Decimal_revapp_ind; subst P; simpl; try reflexivity;
    intros d1'; intros; auto.
Qed.  

Lemma Decimal_Little_succ_double_pos (d : Decimal.uint):
  Decimal.Little.succ_double d <> Decimal.Nil.
Proof.
  destruct d; intro; discriminate.
Qed.

Lemma Decimal_Little_succ_pos (d : Decimal.uint):
  Decimal.Little.succ d <> Decimal.Nil.
Proof.
  destruct d; intro; discriminate.
Qed.

Lemma Decimal_Little_double_pos (d : Decimal.uint):
  d <> Decimal.Nil -> Decimal.Little.double d <> Decimal.Nil.
Proof.
  destruct d; intro; try discriminate.
  intro Hcontra; subst; contradiction.
Qed.

Lemma Pos_to_little_uint_not_Nil (p : positive):
  Pos.to_little_uint p = Decimal.Nil -> False.
Proof.
  induction p; intros H; try discriminate.
  simpl in H.
  - apply Decimal_Little_succ_double_pos in H; contradiction.
  - apply IHp.
    apply Decimal_Little_double_pos in H; try contradiction.
    fold (Pos.to_little_uint p).
    auto.
Qed.

Lemma Pos_to_uint_not_Nil (p : positive):
  Pos.to_uint p <> Decimal.Nil.
Proof.
  unfold Pos.to_uint.
  intro H; rewrite Decimal_rev_nil in H.
  apply Pos_to_little_uint_not_Nil in H.
  assumption.
Qed.
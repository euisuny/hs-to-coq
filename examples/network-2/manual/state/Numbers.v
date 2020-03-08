Require Import Coq.PArith.BinPos Coq.ZArith.BinInt Coq.NArith.BinNat
        Coq.ZArith.Zdiv.
Require Import Omega.

Lemma N_pos_pos (p : positive): (0 < N.pos p)%N.
Proof.
  destruct p; apply N.lt_0_1.
Qed.

Definition N_lt_dec (n1 n2 : N): ({n1 < n2} + {~ n1 < n2})%N.
Proof.
  destruct (N.compare n1 n2) eqn:H.
  - apply N.compare_eq in H.
    subst; right.
    apply N.lt_irrefl.
  - rewrite N.compare_lt_iff in H.
    auto.
  - rewrite N.compare_gt_iff in H.
    right.
    apply N.lt_asymm.
    assumption.
Defined.

Definition N_le_dec (n1 n2 : N): ({n1 <= n2} + {~ n1 <= n2})%N.
Proof.
  destruct (N.compare n1 n2) eqn:H.
  - apply N.compare_eq in H.
    subst; left.
    apply N.le_refl.
  - rewrite N.compare_lt_iff in H.
    left.
    apply N.lt_le_incl.
    assumption.
  - rewrite N.compare_gt_iff in H.
    right.
    apply N.lt_nge.
    assumption.
Defined.

Lemma N_pow_ge_1 (n p : N): (n <> 0 -> (1 <= N.pow n p))%N.
Proof.
  intros Hn.
  transitivity (n^0)%N.
  { rewrite N.pow_0_r. apply N.le_refl. }
  apply N.pow_le_mono_r; auto.
  apply N.le_0_l.
Qed.

Lemma N_pow_ge_0 (n p : N): (n <> 0 -> (0 <= N.pow n p))%N.
Proof.
  intros H.
  pose proof (N_pow_ge_1 n p H).
  transitivity 1%N; auto.
  apply N.le_0_1.
Qed.

Lemma Z_pow_ge_1 (n p : Z): (0 < n -> 0 <= p -> (1 <= Z.pow n p))%Z.
Proof.
  intros Hn.
  transitivity (n^0)%Z.
  { rewrite Z.pow_0_r. apply Z.le_refl. }
  apply Z.pow_le_mono_r; auto.
Qed.

Lemma Z_pow_ge_0 (n p : Z): (0 < n -> 0 <= p -> (0 <= Z.pow n p))%Z.
Proof.
  intros H.
  pose proof (Z_pow_ge_1 n p H).
  transitivity 1%Z; auto.
  apply Z.le_0_1.
Qed.

Lemma N_mod_add_pow (a b c p : N):
  (c <> 0 -> p <> 0 -> ((a + b * c^p) mod c)%N = (a mod c))%N.
Proof.
  intros Hc Hp.
  apply N.neq_0_lt_0 in Hp.
  rewrite <- (N.succ_pred_pos p) by assumption.
  rewrite N.pow_succ_r by apply N.le_0_l.
  rewrite (N.mul_comm c).
  rewrite N.mul_assoc.
  rewrite N.mod_add by assumption.
  reflexivity.
Qed.

Lemma Z_mod_add_pow (a b c p : Z):
  (c <> 0 -> 0 < p -> ((a + b * c^p) mod c)%Z = (a mod c))%Z.
Proof.
  intros Hc Hp.
  rewrite <- (Z.succ_pred p) by assumption.
  rewrite Z.pow_succ_r by omega.
  rewrite (Z.mul_comm c).
  rewrite Z.mul_assoc.
  rewrite Z.mod_add by assumption.
  reflexivity.
Qed.

Lemma N_div_add_pow (a b c p : N):
  (c <> 0 -> p <> 0 -> ((a + b * c^p) / c = a / c + b * c^(p-1)))%N.
Proof.
  intros Hc Hp.
  rewrite <- (N.succ_pred p) by assumption.
  rewrite N.pow_succ_r by apply N.le_0_l.
  rewrite (N.mul_comm c).
  rewrite N.mul_assoc.
  rewrite N.div_add by assumption.
  rewrite <- N.add_1_r.
  rewrite N.add_sub.
  reflexivity.
Qed.

Lemma Z_div_add_pow (a b c p : Z):
  (c <> 0 -> p > 0 -> ((a + b * c^p) / c = a / c + b * c^(p-1)))%Z.
Proof.
  intros Hc Hp.
  rewrite <- (Z.succ_pred p) by assumption.
  rewrite Z.pow_succ_r by omega.
  rewrite (Z.mul_comm c).
  rewrite Z.mul_assoc.
  rewrite Z.div_add by omega.
  rewrite <- Z.add_1_r.
  rewrite Z.add_simpl_r.
  reflexivity.
Qed.

Lemma N_mul_le_mono_l_div_r (a b p : N):
  (0 < p -> a <= b/p -> p * a <= b)%N.
Proof.
  intros Hp Ha.
  apply N.mul_le_mono_nonneg_l with (p := p) in Ha.
  2: { apply N.lt_le_incl. assumption. }
  apply N.le_trans with (p * (b/p))%N; trivial.
  apply N.mul_div_le.
  apply N.neq_0_lt_0.
  assumption.
Qed.

Lemma N_mul_le_mono_l_div_l (a b p : N):
  (0 < p -> a/p <= b -> a <= p * b + (p - 1))%N.
Proof.
  intros Hp Ha.
  apply N.mul_le_mono_nonneg_l with (p := p) in Ha.
  2: { apply N.lt_le_incl. assumption. }
  pose proof Hp as Hp'.
  apply (N.neq_0_lt_0) in Hp.
  pose proof (N.mul_succ_div_gt a p Hp) as H.
  apply N.lt_le_pred in H.
  rewrite N.mul_succ_r in H.
  transitivity (N.pred (p * (a/p) + p))%N; trivial.
  rewrite <- N.sub_1_r.
  rewrite <- N.add_sub_assoc.
  2: { apply N.lt_pred_le.
       simpl.
       trivial.
  }
  apply N.add_le_mono_r.
  trivial.
Qed.

Lemma Z_mul_le_mono_l_div_r (a b p : Z):
  (0 < p -> a <= b/p -> p * a <= b)%Z.
Proof.
  intros Hp Ha.
  apply Z.mul_le_mono_nonneg_l with (p := p) in Ha; try omega.
  apply Z.le_trans with (p * (b/p))%Z; trivial.
  apply Z.mul_div_le; trivial.
Qed.

Lemma Z_mul_le_mono_l_div_l (a b p : Z):
  (0 < p -> a/p <= b -> a <= p * b + (p - 1))%Z.
Proof.
  intros Hp Ha.
  apply Z.mul_le_mono_nonneg_l with (p := p) in Ha; try omega.
  pose proof (Z.mul_succ_div_gt a p Hp) as H.
  apply Zlt_le_succ in H.
  rewrite Z.mul_succ_r in H.
  transitivity (p * (a/p) + p - 1)%Z; omega.
Qed.

Lemma N_mod_p_div_p_0 (n p : N): (0 < p -> n mod p / p = 0)%N.
Proof.
  intros Hp.
  pose proof (N.mod_bound_pos n p (N.le_0_l n) Hp).
  apply N.div_small.
  destruct H; assumption.
Qed.

Module Export LogCeil.

Section Logk.

  Variable (k : N).
  Context `{(1 < k)%N}.

  Lemma div_lt (n : N): (n <> 0 -> n / k < n)%N.
  Proof.
    intros Hn.
    apply N.div_lt.
    - apply N.neq_0_lt_0 in Hn; trivial.
    - assumption.
  Qed.

  Definition log_ceil (n : N): N.
  Proof.
    revert n.
    apply (Fix N.lt_wf_0).
    intros x IH.
    refine (if N.eq_dec x 0%N then 1%N else _).
    refine (if N_lt_dec x k then 1%N else N.succ (IH (x/k)%N _)).
    apply N.div_lt.
    - apply N.neq_0_lt_0 in n. trivial.
    - assumption.
  Defined.

  Lemma log_ceil_zero:
    (log_ceil 0 = 1)%N.
  Proof.
    unfold log_ceil.
    rewrite Fix_eq.
    { reflexivity. }
    intros ? ? ? Hy.
    destruct (N.eq_dec x 0); try reflexivity.
    destruct (N_lt_dec x k); try rewrite Hy; reflexivity.
  Qed.

  Lemma log_ceil_single_digit (n : N):
    (n < k ->
     log_ceil n = 1)%N.
  Proof.
    intros Hn.
    unfold log_ceil.
    rewrite Fix_eq.
    { destruct (N.eq_dec n 0); try reflexivity.
      destruct (N_lt_dec n k).
      { simpl; reflexivity. }
      { contradict Hn. assumption. }
    }
    intros ? ? ? Hy.
    destruct (N.eq_dec x 0); try rewrite Hy; reflexivity.
  Qed.

  Lemma log_ceil_unfold (n : N):
    (k <= n ->
     log_ceil n = N.succ (log_ceil (n / k)))%N.
  Proof.
    intros Hn.
    unfold log_ceil at 1.
    rewrite Fix_eq.
    2: {
      intros x f g Hfg.
      destruct (N.eq_dec x 0); auto.
      rewrite Hfg.
      reflexivity.
    }
    destruct (N.eq_dec n 0).
    { subst. contradict Hn. apply N.lt_nge.
      transitivity 1%N; auto.
      apply N.lt_0_1.
    }
    destruct (N_lt_dec n k).
    { contradict Hn. apply N.lt_nge. assumption. }
    f_equal.
  Qed.

  Lemma log_ceil_nonzero (n : N): (log_ceil n <> 0)%N.
  Proof.
    destruct (N_lt_dec n k) as [Hlt | Hnlt].
    { rewrite log_ceil_single_digit; try assumption.
      intro; discriminate.
    }
    rewrite log_ceil_unfold.
    2: { apply N.nlt_ge. assumption. }
    apply N.succ_0_discr.
  Qed.

  Lemma log_ceil_upper_bound (n : N):
    (n <= k^(log_ceil n) - 1)%N.
  Proof.
    revert n.
    apply (Fix (N.lt_wf_0)).
    intros x Hy; simpl.
    destruct (N_lt_dec x k) as [l | nl].
    { rewrite log_ceil_single_digit; try apply l.
      rewrite N.pow_1_r.
      rewrite N.sub_1_r.
      apply N.lt_le_pred.
      assumption.
    }
    rewrite log_ceil_unfold.
    2: { apply N.le_ngt. assumption. }

    assert (k <> 0%N).
    { intro k_eq. pose proof H as Hk. rewrite k_eq in Hk.
      discriminate.
    }

    destruct (N.eq_dec x 0) as [eq0 | neq0].
    { subst.
      rewrite N.div_0_l by assumption.
      rewrite log_ceil_zero.
      rewrite N.sub_1_r.
      apply N.le_0_l.
    }
    specialize (Hy (x/k)%N (div_lt x neq0)).
    apply N_mul_le_mono_l_div_l in Hy.
    2: { transitivity 1%N; auto. apply N.lt_0_1. }
    eapply N.le_trans; [ apply Hy |].
    rewrite N.mul_sub_distr_l.
    rewrite <- N.pow_succ_r.
    2: { apply N.le_0_l. }
    simpl N.mul.
    simpl.
    match goal with
    | |- (?x <= ?y)%N => replace x with y; [apply N.le_refl |]
    end.

    apply N2Z.inj.
    rewrite N2Z.inj_sub.
    2: { apply N_pow_ge_1.
         assumption.
    }
    rewrite N2Z.inj_add.
    rewrite N2Z.inj_sub.
    2: {
      replace (k * 1)%N with (k^1)%N by reflexivity.
      apply N.pow_le_mono_r; try assumption.
      apply N.le_pred_le_succ.
      simpl.
      apply N.le_0_l.
    }
    simpl.
    rewrite N2Z.inj_mul.
    rewrite N2Z.inj_sub.
    2: { apply N.lt_le_incl. assumption. }
    simpl.
    omega.
  Qed.

  Lemma log_ceil_lower_bound (n : N):
    (k <= n ->
     k^(N.pred (log_ceil n)) <= n)%N.
  Proof.
    revert n.
    set (P n := (k <= n ->
                 k ^ N.pred (log_ceil n) <= n)%N).
    apply (Fix (N.lt_wf_0) P).
    intros x Hy; subst P; simpl.
    intro Hx.
    destruct (N_lt_dec x k) as [l | nl].
    { contradict l.
      apply N.le_ngt.
      assumption.
    }
    rewrite log_ceil_unfold.
    2: { apply N.le_ngt. assumption. }

    assert (k <> 0%N).
    { intro k_eq. pose proof H as Hk. rewrite k_eq in Hk.
      discriminate.
    }

    destruct (N.eq_dec x 0) as [eq0 | neq0].
    { subst.
      contradict nl.
      apply N.neq_0_lt_0; assumption.
    }
    simpl in Hy.
    specialize (Hy (x/k)%N (div_lt x neq0)).
    destruct (N_le_dec k (x/k)) as [le_k | nle_k].
    2: {
      rewrite log_ceil_single_digit.
      2: { apply N.lt_nge in nle_k. assumption. }
      rewrite N.pred_succ.
      rewrite N.pow_1_r.
      assumption.
    }
    specialize (Hy le_k).
    apply N_mul_le_mono_l_div_r in Hy.
    2: { apply N.neq_0_lt_0. assumption. }
    rewrite <- N.pow_succ_r in Hy.
    2: { apply N.le_0_l. }
    rewrite N.succ_pred in Hy.
    2: { rewrite log_ceil_unfold by assumption.
         apply N.neq_succ_0.
    }
    rewrite N.pred_succ.
    assumption.
  Qed.

  Lemma most_significant_exists (n : N):
    (n <> 0 ->
     exists p, k^p <= n <= k^(p + 1) - 1)%N.
  Proof.
    intro Hn.
    exists (N.pred (log_ceil n)).
    destruct (N_lt_dec n k) as [ | n_ge].
    {
      rewrite log_ceil_single_digit by assumption.
      rewrite N.pow_1_r.
      split.
      - simpl. apply N.neq_0_lt_0 in Hn.
        apply N2Z.inj_lt in Hn; simpl in Hn.
        apply N2Z.inj_le; simpl.
        omega.
      - apply N2Z.inj_lt in l.
        apply N2Z.inj_le.
        rewrite N2Z.inj_sub.
        2: { apply N.lt_le_incl. assumption. }
        simpl.
        omega.
    }

    apply N.nlt_ge in n_ge.
    pose proof (@log_ceil_lower_bound n n_ge) as Hlb.
    pose proof (@log_ceil_upper_bound n) as Hub.
    rewrite N.add_1_r.
    rewrite N.succ_pred.
    2: { apply log_ceil_nonzero. }
    split; auto.
  Qed.

  Lemma most_significant_le (n p q: N):
    (k^p <= n < k^(p + 1) ->
     n < k^q -> p + 1 <= q)%N.
  Proof.
    intros [Hlower Hupper] Hq.
    destruct (N_lt_dec q (p + 1)).
    2: {
      apply N.nlt_ge in n0.
      intros; assumption.
    }

    rewrite N.add_1_r in l.
    rewrite N.lt_succ_r in l.
    apply (N.pow_le_mono_r k) in l.
    2: { apply N.neq_0_lt_0. transitivity 1%N; try assumption. apply N.lt_0_1. }
    contradict Hq.
    apply N.nlt_ge.
    transitivity (k^p)%N; assumption.
  Qed.

  Lemma most_significant_ge (n p q: N):
    (k^p <= n < k^(p + 1) ->
     k^q <= n -> q <= p)%N.
  Proof.
    intros [Hlower Hupper] Hq.
    destruct (N_le_dec q p).
    { trivial. }
    rewrite N.nle_gt in n0.
    apply N.succ_lt_mono in n0.
    apply (N.pow_lt_mono_r k) in n0; try assumption.
    rewrite <- !N.add_1_r in n0.
    assert (n < k^(q+1))%N as Hn.
    { transitivity (k^(p+1))%N; auto. }
    apply N.succ_le_mono.
    rewrite <- !N.add_1_r.
    apply (most_significant_le n q (p + 1)); auto.
  Qed.

End Logk.

Section PowK.

  Variable (k : Z).
  Context `{(1 < k)%Z}.

  Lemma Z_pow_div (p q : Z):
    (1 <= p -> p <= q ->
     ((k ^ p) | (k ^ q)))%Z.
  Proof.
    intros.
    destruct (Z.le_exists_sub _ _ H1) as [a [Hpq Ha]].
    rewrite Hpq.
    rewrite Z.pow_add_r; try omega.
    apply Z.divide_factor_r.
  Qed.

  Lemma Z_mod_pow_0_mod_pow_0 (n p q : Z):
    (0 <= q -> q <= p ->
     n mod k^p = 0 -> n mod k^q = 0)%Z.
  Proof.
    intros.
    apply Z.mod_divide in H2.
    2: { intro Hcontra.
         pose proof (Z.pow_pos_nonneg k p) as Hkp.
         rewrite Hcontra in Hkp.
         assert (Hk: (0 < k)%Z) by omega.
         assert (Hp: (0 <= p)%Z) by omega.
         specialize (Hkp Hk Hp).
         omega.
    }
    destruct (q <=? 0)%Z eqn:Hq.
    { apply Z.leb_le in Hq.
      assert (q = 0)%Z by omega; subst.
      simpl.
      apply Z.mod_1_r.
    }
    apply Z.leb_gt in Hq.

    apply Z.mod_divide.
    { intro Hcontra.
      pose proof (Z.pow_pos_nonneg k q) as Hkq.
      rewrite Hcontra in Hkq.
      assert (Hk: (0 < k)%Z) by omega.
      specialize (Hkq Hk H0).
      omega.
    }
    apply Z.divide_trans with (k^p)%Z; auto.
    apply Z_pow_div; omega.
  Qed.

  Lemma Z_mod_divide_general (a b m : Z):
    m <> 0%Z ->
    (a mod m = b mod m)%Z <-> (m | (b - a))%Z.
  Proof.
    intros.
    split.
    2: { intros Hdivides.
         unfold Z.divide in Hdivides.
         destruct Hdivides as [n Hn].
         apply Zminus_eq.
         rewrite Z.sub_move_r in Hn.
         subst b.
         rewrite Z.add_comm.
         rewrite Z_mod_plus_full.
         rewrite Z.sub_diag.
         reflexivity.
    }
    intros Hmod.
    rewrite (Z.div_mod b m) by omega.
    rewrite (Z.div_mod a m) by omega.
    rewrite Hmod.
    rewrite Z.add_sub_swap.
    rewrite Z.sub_add_distr.
    rewrite Z.sub_add.
    rewrite <- Z.mul_sub_distr_l.
    apply Z.divide_factor_l.
  Qed.

  Lemma Z_mod_pow_mod_absorb (n p q: Z):
    (0 <= q -> q <= p -> (n mod (k^p)) mod k^q = n mod k^q)%Z.
  Proof.
    intros Hq Hqp.
    apply Z_mod_divide_general.
    { intro. pose proof (Z_pow_ge_1 k q). omega. }
    rewrite (Z.div_mod n (k^p)%Z) at 1.
    2: { intro. pose proof (Z_pow_ge_1 k p). omega. }
    rewrite Z.add_simpl_r.
    apply (Z.divide_trans _ (k^q * (n/k^p))%Z).
    { apply Z.divide_factor_l. }
    apply Z.mul_divide_mono_r.
    destruct (0 <? q)%Z eqn:Hpos.
    { apply Z.ltb_lt in Hpos.
      apply Z_pow_div; omega.
    }
    apply Z.ltb_ge in Hpos.
    assert (q = 0)%Z by omega; subst q.
    rewrite Z.pow_0_r.
    apply Z.divide_1_l.
  Qed.

End PowK.

End LogCeil.
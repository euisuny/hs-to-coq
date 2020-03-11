(* Equality on itrees considered "up to taus" *)

From Coq Require Import
     Setoid Morphisms ProofIrrelevance.

From DeepWeb.Free.Monad Require Import
     Free
     Eq.Eq.
Local Open Scope itree_scope.

(* [untau s t] if [s = Tau (Tau (... Tau t ...))] *)
Inductive untau {E R} : relation (itree E R) :=
| OneTau : forall s t, untau s t -> untau (Tau s) t
| NoTau : forall s, untau s s.

(* Equivalence up to tau ("eq_utt") *)
CoInductive eq_utt {E R} : relation (itree E R) :=
(* Equality with spin is undecidable,
   but one can coinductively generate a proof with this. *)
| EquivTau : forall s t,
    eq_utt s t ->
    eq_utt (Tau s) (Tau t)
| EquivTauExhaust : forall s s' t t',
    untau s s' ->
    untau t t' ->
    eq_notau s' t' ->
    eq_utt s t

with

eq_notau {E R} : relation (itree E R) :=
| EquivRet : forall x, eq_notau (Ret x) (Ret x)
| EquivVis : forall Y (e : E Y) (k1 k2 : Y -> itree E R),
    (forall y, eq_utt (k1 y) (k2 y)) ->
    eq_notau (Vis e k1) (Vis e k2).

Delimit Scope eq_utt_scope with eq_utt.
Infix "=" := eq_utt : eq_utt_scope.

Lemma eq_itree_utt {E R} : forall (s s' : itree E R),
    eq_itree s s' -> eq_utt s s'.
Proof.
  cofix self.
  intros s s' [].
  + econstructor; constructor.
  + econstructor; constructor. auto.
  + constructor. auto.
Qed.

Instance Reflexive_eq_utt {E R} : Reflexive (@eq_utt E R).
Proof.
  intro h.
  apply eq_itree_utt.
  reflexivity.
Qed.

(* NB: eq_notau is not reflexive for Taus. *)

Lemma eq_utt_sym {E R} :
  forall (s t : itree E R),
    eq_utt s t -> eq_utt t s
with
eq_notau_sym {E R} :
  forall (s t : itree E R),
    eq_notau s t -> eq_notau t s.
Proof.
  { intros s t []; econstructor; eauto. }
  { intros s t []; constructor; auto. }
Qed.

Instance Symmetric_eq_utt {E R} : Symmetric (@eq_utt E R).
Proof. exact eq_utt_sym. Qed.

Instance Symmetric_eq_notau {E R} : Symmetric (@eq_notau E R).
Proof. exact eq_notau_sym. Qed.

Lemma pop_tau {E R} :
  forall (s t : itree E R),
    eq_utt s (Tau t) -> eq_utt s t.
Proof.
  cofix self.
  intros s t H.
  inversion H. destruct H2.
  - constructor. apply self. constructor. auto.
  - econstructor; [ constructor | | ]; eauto.
  - econstructor; eauto. destruct H2; inversion H1; auto.
Qed.

Lemma push_tau {E R} :
  forall (s t : itree E R),
    eq_utt s t -> eq_utt s (Tau t).
Proof.
  cofix self.
  intros s t H.
  inversion H.
  - constructor. apply self. auto.
  - econstructor; eauto. constructor. auto.
Qed.

Lemma tau_notau {E R} :
  forall (s t t' u' : itree E R),
    eq_utt s t ->
    untau t t' ->
    eq_notau t' u' ->
    exists s', untau s s' /\ eq_notau s' t'.
Proof.
  intros s t t' u' Hst Htt' Ht'u'.
  induction Htt'.
  - apply IHHtt'; auto.
    apply pop_tau; auto.
  - destruct Hst; inversion Ht'u'; subst;
      exists s'; split; auto; inversion H0; subst; auto.
Qed.

Lemma eq_utt_untau {E R} : forall (s s' : itree E R),
    untau s s' -> eq_utt s s'.
Proof.
  intros s s' H.
  induction H.
  - symmetry. apply push_tau. symmetry. assumption.
  - reflexivity.
Qed.

Lemma untau_inj {E R} :
  forall (s s' s'' t' t'' : itree E R),
    untau s s' ->
    untau s s'' ->
    eq_notau t' s' ->
    eq_notau s'' t'' ->
    s' = s''.
Proof.
  intros s s' s'' t' t'' H.
  induction H; intros H' Hts' Hst''; inversion H'; auto;
    (inversion Hst''; inversion Hts'; subst; discriminate).
Qed.

Lemma eq_utt_trans {E R} :
  forall (s t u : itree E R),
    eq_utt s t -> eq_utt t u -> eq_utt s u
with
eq_notau_trans {E R} :
  forall (s t u : itree E R),
    eq_notau s t -> eq_notau t u -> eq_notau s u.
Proof.
  { intros s t u
           [ s1 t1 H1 | s1 s1' t1 t1' ]
           H2;
      inversion H2 as [ t2 u2 H2' | t2 t2' u2 u2' Ht2 Hu2 H2' ];
      subst.
    - (* Tau, Tau, Tau *) constructor; eapply eq_utt_trans; eauto.
    - (* Tau, Tau & _, _ *)
      apply push_tau in H1.
      pose (Hs1t1 := tau_notau _ _ _ _ H1 Ht2 H2').
      destruct Hs1t1 as [s' [Hs1 Hs't2']].
      econstructor.
      + constructor; eassumption.
      + eassumption.
      + eapply eq_notau_trans; eassumption.
    - (* _, _ & Tau, Tau *)
      symmetry in H2.
      apply eq_notau_sym in H1.
      pose (Ht1u := tau_notau _ _ _ _ H2 H0 H1).
      destruct Ht1u as [s' [Hu Hs't1']].
      econstructor.
      + eassumption.
      + eassumption.
      + eapply eq_notau_trans; apply eq_notau_sym; eassumption.
    - (* _, _, _ *)
      econstructor; try eassumption.
      eapply eq_notau_trans. eassumption.
      replace t2' with t1' in *.
      + auto.
      + eapply untau_inj; eauto.
  }
  { intros s t u Hst Htu.
    destruct Hst; inversion Htu; subst.
    - constructor; auto.
    - apply inj_pair2 in H2.
      apply inj_pair2 in H3.
      subst.
      constructor.
      intros.
      eapply eq_utt_trans; eauto.
  }
Qed.

Instance Transitive_eq_utt {E R} : Transitive (@eq_utt E R).
Proof. exact eq_utt_trans. Qed.

Instance Transitive_eq_notau {E R} : Transitive (@eq_notau E R).
Proof. exact eq_notau_trans. Qed.

Instance Equivalence_eq_utt {E R} : Equivalence (@eq_utt E R).
Proof. constructor; typeclasses eauto. Qed.

Add Parametric Relation E R : (itree E R) eq_utt
  reflexivity proved by Reflexive_eq_utt
  symmetry proved by Symmetric_eq_utt
  transitivity proved by Transitive_eq_utt
    as eq_utt_rel.

Lemma untau_tau E R : forall s s' : itree E R,
    untau s (Tau s') -> untau s s'.
Proof.
  fix IH 3.
  intros s s' H.
  inversion_clear H as [ s0 s0' H0 | ].
  - constructor. apply IH. assumption.
  - repeat constructor.
Qed.

Lemma untau_trans E R : forall s t u : itree E R,
    untau s t -> untau t u -> untau s u.
Proof.
  fix IH 4.
  intros s t u Hst Htu.
  inversion_clear Hst as [ s0 s0' Hst0 | ].
  - constructor. eapply IH; eauto.
  - auto.
Qed.

Lemma untau_eq_utt E R : forall s s' t t' : itree E R,
    untau s s' ->
    untau t t' ->
    eq_utt s' t' ->
    eq_utt s t.
Proof.
  cofix self.
  intros s s' t t' Hs Ht Hst'.
  destruct Hst'.
  - inversion Hs; inversion Ht; subst.
    + constructor. eapply self; try eassumption.
      constructor. assumption.
    + constructor. eapply self.
      * apply untau_tau. eauto.
      * constructor.
      * auto.
    + constructor. eapply self.
      * constructor.
      * apply untau_tau. eauto.
      * auto.
    + constructor. auto.
  - econstructor.
    + eapply untau_trans; eauto.
    + eapply untau_trans; eauto.
    + auto.
Qed.

Lemma untau_bind E R S :
  forall s s' (k : R -> itree E S),
    untau s s' -> untau (Core.bind_itree s k) (Core.bind_itree s' k).
Proof.
  fix IH 4.
  intros s x k H.
  inversion_clear H as [ s0 s0' H' | ].
  - rewrite core_bind_def. simpl.
    constructor. apply IH. auto.
  - rewrite core_bind_def. simpl.
    repeat constructor.
Qed.

(* We decompose the handling of [bindM] by
   first proving congruence of [Core.bindM]. *)

Ltac dispatch :=
  try (eapply untau_trans;
       [ eapply untau_bind; eauto
       | rewrite core_bind_def; do 2 constructor ]).

Add Parametric Morphism E R S :
  (@Core.bind_itree E R S)
    with signature
    (eq_utt ==> pointwise_relation _ eq_utt ==> eq_utt)
      as core_bind_mor.
Proof.
  intros s1 s2 Hs k1 k2 Hk.
  generalize dependent s1.
  generalize dependent s2.
  cofix bind_mor. (* Recurse in the Tau case. *)
  intros.
  destruct Hs.
  - (* Tau *)
    do 2 rewrite core_bind_def.
    constructor.
    auto.
  - (* -> ~Tau *)
    destruct H1.
    + (* -> Ret *)
      eapply untau_eq_utt; dispatch.
      eauto.
    + (* -> Vis *)
      econstructor; dispatch.
      constructor. auto.
Qed.

Add Parametric Morphism E R S :
  (@bind_itree E R S)
    with signature
    (eq_utt ==> pointwise_relation _ eq_utt ==> eq_utt)
      as bind_mor.
Proof.
  intros.
  unfold bind_itree.
  apply core_bind_mor.
  - auto.
  - constructor. auto.
Qed.

Lemma core_bind_bind {E R S T} :
  forall (s : itree E R) (k : R -> itree E S) (h : S -> itree E T),
    ( (s >>=0 k) >>=0 h
      =
      s >>=0 (fun r => k r >>=0 h)
    )%eq_utt.
Proof.
  intros.
  apply eq_itree_utt.
  apply Eq.core_bind_bind.
Qed.

(* Associativity actually holds structurally. *)
Lemma bind_bind {E R S T} :
  forall (s : itree E R) (k : R -> itree E S) (h : S -> itree E T),
    (((s >>= k) >>= h) = (s >>= (fun x => k x >>= h)))%eq_utt.
Proof.
  intros.
  apply eq_itree_utt.
  apply Eq.bind_bind.
Qed.

Lemma bind_ret {E R} :
  forall s : itree E R,
    (s >>= Ret = s)%eq_utt.
Proof.
  cofix bind_ret.
  intros s.
  unfold bind_itree in *.
  rewrite core_bind_def.
  destruct s; simpl.
  - apply pop_tau; reflexivity.
  - econstructor; try apply NoTau.
    constructor; auto.
  - constructor; auto.
Qed.

From Coq Require Import
     Relations
     Setoid
     Morphisms
     Program.

From Custom Require Import
     Monad.
Import MonadNotations.

From DeepWeb.Free.Monad Require Import
     Free
     Eq.Eq.

Local Notation TyCon := (Type -> Type).

Section Stutter.

Context {E : TyCon} {R : Type}.

CoInductive stutter : relation (itree E R) :=
| stutter_Ret x :
    stutter (Ret x) (Ret x)
| stutter_Tau t1 t2 :
    stutter t1 t2 -> stutter (Tau t1) (Tau t2)
| stutter_stutter t1 t2 :
    stutter t1 t2 -> stutter (Tau t1) t2
| stutter_Vis X (e : E X) k1 k2 :
    (forall x, stutter (k1 x) (k2 x)) ->
    stutter (Vis e k1) (Vis e k2)
.

CoFixpoint stutter_refl t : stutter t t.
Proof.
  destruct t; constructor; auto.
Qed.

(* Easier to apply *)
Definition stutter_refl' t1 t2 :
  t1 = t2 -> stutter t1 t2.
Proof.
  intros []; apply stutter_refl.
Defined.

CoFixpoint stutter_trans t1 t2 t3 :
  stutter t1 t2 -> stutter t2 t3 -> stutter t1 t3.
Proof.
  intros H1 H2.
  destruct H1; inversion H2; subst.
  - constructor.
  - constructor.
    eapply stutter_trans; eauto.
  - constructor.
    eapply stutter_trans; eauto.
  - constructor; auto.
  - apply stutter_stutter.
    eapply stutter_trans; eauto.
  - constructor.
    eapply stutter_trans; eauto.
  - constructor.
    eapply stutter_trans; eauto.
  - apply inj_pair2 in H3.
    apply inj_pair2 in H4.
    subst.
    constructor.
    intro x.
    eapply stutter_trans; eauto.
Defined.

Add Parametric Relation : (itree E R) stutter
  reflexivity proved by stutter_refl
  transitivity proved by stutter_trans
  as stutter_rel.

Add Parametric Morphism : (@Tau _ _)
    with signature (stutter ==> stutter)
      as Tau_mor.
Proof.
  intros t1 t2 H. constructor. apply H.
Defined.

Lemma stutter_once t : stutter (Tau t) t.
Proof.
  apply stutter_stutter, stutter_refl.
Defined.

Add Parametric Morphism X (e : E X) : (@Vis _ _ _ e)
    with signature (pointwise_relation _ stutter ==> stutter)
      as Vis_mor.
Proof.
  intros k1 k2 H. constructor. apply H.
Defined.

End Stutter.

Add Parametric Morphism {E : TyCon} A B :
  (@Core.bind_itree E A B)
    with signature
    (stutter ==> pointwise_relation _ stutter ==> stutter)
      as core_bind_itree_mor.
Proof.
  intros t1 t2 Ht k1 k2 Hk.
  generalize dependent t2.
  generalize dependent t1.
  cofix stutter_bindM.
  intros t1 t2 Ht.
  destruct Ht.
  - do 2 rewrite core_bind_def.
    apply Hk.
  - do 2 rewrite core_bind_def.
    constructor; apply stutter_bindM.
    apply Ht.
  - rewrite core_bind_def.
    constructor. apply stutter_bindM.
    apply Ht.
  - do 2 rewrite core_bind_def.
    constructor.
    intro x.
    apply stutter_bindM.
    apply H.
Defined.

Add Parametric Morphism E A B :
  (@Core.bind_itree E A B)
    with signature (stutter ==> eq ==> stutter)
      as core_bind_itree_mor2.
Proof.
  intros; apply core_bind_itree_mor; auto.
  intro b; apply stutter_refl.
Defined.

Add Parametric Morphism {E : TyCon} A B :
  (@bind_itree E A B)
    with signature
    (stutter ==> pointwise_relation _ stutter ==> stutter)
      as bind_itree_mor.
Proof.
  intros.
  unfold bind_itree.
  apply core_bind_itree_mor.
  apply H.
  intro w.
  constructor.
  apply H0.
Defined.

Add Parametric Morphism {E : TyCon} A B :
  (@bind_itree E A B)
    with signature
    (stutter ==> eq ==> stutter)
      as bind_itree2_mor.
Proof.
  intros.
  unfold bind_itree.
  apply core_bind_itree_mor.
  apply H.
  intro w.
  constructor.
  apply stutter_refl.
Defined.

Add Parametric Morphism {E : TyCon} A :
  (@stutter E A)
    with signature
    (flip stutter ==> stutter ==> impl)
      as stutter_mor.
Proof.
  intros t1 t1' H1 t2' t2 H2 H.
  eapply stutter_trans; [eapply stutter_trans |]; eauto.
Defined.

Lemma eq_itree_stutter {E : TyCon} {R} :
  forall (t1 t2 : itree E R),
    (t1 = t2)%eq_itree -> stutter t1 t2.
Proof.
  cofix eq_itree_stutter.
  intros t1 t2 Ht.
  inversion Ht; constructor; auto.
Defined.

Instance subrelation_eq_itree_stutter E R :
  subrelation (@eq_itree E R) stutter.
Proof.
  unfold subrelation.
  apply eq_itree_stutter.
Defined.

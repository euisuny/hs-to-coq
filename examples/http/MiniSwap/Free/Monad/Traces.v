From Coq Require Import
     Program Setoid Morphisms.

From Custom Require Import
     List Monad.
Import ListNotations.
Import MonadNotations.

From DeepWeb.Free.Monad Require Import
     Free OpenUnion Common Eq.Eq Eq.Utt Eq.Stutter.

(* Itrees are annotated with _effects_ [e : E X]. We call _event_
   the pair of an effect together with a response [x : X]. *)
Variant event (E : Type -> Type) : Type :=
| Event : forall X, E X -> X -> event E.

Arguments Event {E X} _ _.

Section Traces.

(* We assume a separation of effects into visible ones (named [F])
   and invisible ones (named [E], which usually represents
   internal nondeterminism). *)

Variable E : Type -> Type. (* Invisible effects *)
Variable F : Type -> Type. (* Visible effects *)

(* Traces are lists of visible events. *)
Definition trace := list (event F).

(* Trace semantics of itrees:
   A trace in an itree is a path (made of nodes [e : F X] with edges
   [x : X], i.e., [events]), from which the "invisible" effects
   have been erased.
   This relation is also indexed by the value of a [Ret] leaf
   at the end of that path, if any (hence it is an [option R]).

   [is_trace tr r_ t]: there is a path in the tree [t] with visible
   events [tr] and potential result [r_].
 *)
Inductive is_trace {R : Type} :
  itree (E +' F) R -> trace -> option R -> Prop :=

(* Our trace semantics are prefix-closed: we can stop observation
   at any time. Then there is no leaf result to see. *)
| Trace_Empty : forall m, is_trace m [] None

(* A leaf has only an empty trace and a result. *)
| Trace_Ret : forall r, is_trace (Ret r) [] (Some r)

(* [Tau] can be viewed as a kind of invisible event. *)
| Trace_Tau : forall t m r,
    is_trace m t r -> is_trace (Tau m) t r

(* Invisible events are not recorded in the trace. *)
| Trace_Invis : forall X (e : E X) x t k r,
    is_trace (k x) t r -> is_trace (Vis (e |) k) t r

(* Visible events are recorded in the trace. *)
| Trace_Vis : forall Y (e : F Y) y t k r,
    is_trace (k y) t r ->
    is_trace (Vis (inr e) k) (Event e y :: t) r
.

(* Trace inclusion between itrees [m] and [m']:
   every trace of [m] is a trace of [m'], with the same results [r]. *)
Definition trace_incl {R : Type} (m m' : itree (E +' F) R) : Prop :=
  forall t r,
    is_trace m t r -> is_trace m' t r.

(* Trace equivalence: the itrees [m] and [m'] have the same traces. *)
Definition trace_eq {R : Type} (m m' : itree (E +' F) R) : Prop :=
  forall t r,
    is_trace m t r <-> is_trace m' t r.

End Traces.

Arguments Event {E X} _ _.
Arguments is_trace {E F R} _ _ _.
Arguments trace_incl {E F R} _ _.
Arguments trace_eq {E F R} _ _.

Module Export TracesNotations.

Delimit Scope trace_scope with trace.
Infix "<=" := trace_incl : trace_scope.
Infix "=" := trace_eq : trace_scope.

End TracesNotations.

Local Notation TyCon := (Type -> Type).

(* Trace equivalence is trace inclusion both ways, of course. *)
Lemma trace_eq_incl2 {E F : TyCon} {R : Type}
      (m m' : itree (E +' F) R) :
  trace_incl m m' /\ trace_incl m' m <-> trace_eq m m'.
Proof.
  split.
  - intros H t; split; apply H.
  - intros H; split; intro t; apply H.
Qed.

(* Trace inclusion is reflexive. *)
Lemma trace_incl_refl {E F : TyCon} {R : Type}
      (m : itree (E +' F) R) :
  trace_incl m m.
Proof. intro; auto. Qed.

(* Trace inclusion is transitive. *)
Lemma trace_incl_trans {E F : TyCon} {R: Type}
      (m n p : itree (E +' F) R) :
  trace_incl m n -> trace_incl n p -> trace_incl m p.
Proof. intros; intro; auto. Qed.

(* We import [inj_pair2] to take care of some heterogeneous
   equalities. *)
Import ProofIrrelevance.

Lemma trace_incl_eutt {E F : TyCon} {R : Type}
      (m m' : itree (E +' F) R) :
  eq_utt m m' -> trace_incl m m'.
Proof.
  intros H t r Ht.
  generalize dependent m'.
  induction Ht; intros m' H.
  - constructor.
  - inversion H; subst; clear H.
    induction H1.
    + constructor.
      apply IHuntau.
      auto.
    + inversion H0; subst.
      inversion H2; subst.
      constructor.
  - apply IHHt.
    symmetry; apply pop_tau; symmetry; apply H.
  - inversion_clear H.
    inversion H0. subst.
    inversion H2.
    apply inj_pair2 in H4.
    apply inj_pair2 in H5.
    subst.
    remember (Vis _ _) as s' in H1.
    induction H1.
    + constructor. auto.
    + subst. econstructor. eauto.
  - inversion_clear H.
    inversion H0. subst.
    inversion H2.
    apply inj_pair2 in H4.
    apply inj_pair2 in H5.
    subst.
    remember (Vis _ _) in H1.
    induction H1.
    + constructor. auto.
    + subst. constructor. auto.
Qed.

Lemma trace_incl_respects_bind_assoc {E F X Y Z}
      (m : itree (E +' F) X)
      (f : X -> itree (E +' F) Y) (g : Y -> itree (E +' F) Z)
      (t : itree (E +' F) Z) :
    trace_incl ( b <- (a <- m ;; f a) ;; g b ) t ->
    trace_incl ( a <- m ;; b <- f a ;; g b ) t.
Proof.
  intros.
  simpl.
  eapply trace_incl_trans.
  - apply trace_incl_eutt.
    symmetry.
    apply bind_bind.
  - assumption.
Qed.

Lemma trace_or_incl {E F : TyCon} {R : Type} `{nondetE -< E}
      (k1 k2 : itree (E +' F) R):
  trace_incl k1 (or k1 k2) /\ trace_incl k2 (or k1 k2).
Proof.
  intros.
  unfold trace_incl; split; intros; unfold or;
    [ apply Trace_Invis with (x := true)
    | apply Trace_Invis with (x := false)]; assumption.
Qed.

Lemma eutt_bind_or {E F : TyCon} {X Y : Type} `{nondetE -< E}
      (m1 m2 : itree (E +' F) X) (k : X -> itree (E +' F) Y) :
  eq_utt (x <- or m1 m2 ;; k x)
         (or (x <- m1 ;; k x)
             (x <- m2 ;; k x)).
Proof.
  rewrite (match_itree (bind (or _ _) (fun x => k x))).
  unfold or.
  simpl.
  eapply EquivTauExhaust; try constructor.
  intros.
  destruct y; reflexivity.
Qed.

Lemma trace_or_incl_bind {E F : TyCon} {X Y : Type} `{HE: nondetE -< E}
      (m1 m2 : itree (E +' F) X) (k : X -> itree (E +' F) Y):
  trace_incl (x <- m1 ;; k x)
             (x <- or m1 m2 ;; k x) /\
  trace_incl (x <- m2 ;; k x)
             (x <- or m1 m2 ;; k x).
Proof.
  pose proof (eutt_bind_or m1 m2 k) as H.
  symmetry in H.
  apply trace_incl_eutt in H.
  destruct (trace_or_incl (x <- m1 ;; k x) (x <- m2 ;; k x))
    as [HIncl1 HIncl2].
    split; eapply trace_incl_trans; eassumption.
Qed.

Lemma trace_or_incl_bind1 {E F : TyCon} {X Y : Type} `{nondetE -< E}
      (m1 m2 : itree (E +' F) X) (k : X -> itree (E +' F) Y):
  trace_incl (x <- m1 ;; k x)
             (x <- or m1 m2 ;; k x).
Proof. destruct (trace_or_incl_bind m1 m2 k); assumption. Qed.

Lemma trace_or_incl_bind2 {E F : TyCon} {X Y : Type} `{nondetE -< E}
      (m1 m2 : itree (E +' F) X) (k : X -> itree (E +' F) Y):
  trace_incl (x <- m2 ;; k x)
             (x <- or m1 m2 ;; k x).
Proof. destruct (trace_or_incl_bind m1 m2 k); assumption. Qed.

Lemma trace_choose_incl {E F X R} `{nondetE -< E} `{failureE -< E}
      (x : X) (l : list X) (k : X -> itree (E +' F) R) :
  In x l -> trace_incl (k x) (x <- choose l ;; k x).
Proof.
  generalize dependent k.
  induction l; intros k HIn; unfold choose;
    inversion HIn.
  - subst.
    eapply trace_incl_trans; [| apply trace_or_incl_bind1].
    apply trace_incl_eutt.
    symmetry.
    simpl.
    rewrite ret_bind.
    symmetry.
    apply push_tau.
    reflexivity.
  - eapply trace_incl_trans; [| apply trace_or_incl_bind2].
    apply IHl.
    assumption.
Qed.

(* When the result [r : R] does not matter, we can have one
   fewer constructor. *)
Inductive is_trace' {E F : TyCon} {R : Type} :
  itree (E +' F) R -> trace F -> Prop :=
| TraceEmpty : forall s, is_trace' s []
| TraceTau : forall s tr, is_trace' s tr -> is_trace' (Tau s) tr
| TraceInvis : forall X e k (x : X) tr,
    is_trace' (k x) tr ->
    is_trace' (Vis (e |) k) tr
| TraceVis : forall X (e : F X) x k tr,
    is_trace' (k x) tr ->
    is_trace' (Vis (| e) k) (Event e x :: tr)
.

Lemma is_trace_is_trace' {E F : TyCon} {R : Type}
      (t : itree (E +' F) R) r tr :
  is_trace t tr r -> is_trace' t tr.
Proof.
  induction 1; econstructor; eauto.
Qed.

Lemma is_trace'_is_trace {E F : TyCon} {R : Type}
      (t : itree (E +' F) R) tr :
  is_trace' t tr -> is_trace t tr None.
Proof.
  induction 1; econstructor; eauto.
Qed.

Add Parametric Morphism E F R : (@is_trace' E F R) with signature
    (stutter ==> eq ==> impl) as is_trace'_mor.
Proof.
  intros x y Hm tr Hob.
  generalize dependent y.
  induction Hob.
  + constructor.
  + intros. inversion Hm.
    * constructor; auto.
    * auto.
  + intros. inversion Hm.
    apply inj_pair2 in H1. rewrite H1.
    econstructor. apply IHHob.
    apply inj_pair2 in H2. rewrite <- H2.
    apply H3.
  + intros. inversion Hm.
    apply inj_pair2 in H1. rewrite H1.
    constructor. apply IHHob.
    apply inj_pair2 in H2. rewrite <- H2.
    apply H3.
Qed.

Add Parametric Morphism E F R : (@is_trace' E F R) with signature
    (Eq.eq_itree ==> eq ==> impl) as is_trace'_eq_mor.
Proof.
  intros.
  apply is_trace'_mor; auto.
  apply eq_itree_stutter; auto.
Qed.

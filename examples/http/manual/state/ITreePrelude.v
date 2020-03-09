Require Import FunctionalExtensionality.

From ExtLib Require Export Structures.Monad.
From ITree Require Export ITree.
From ITree.Events Require Export Nondeterminism Exception.
From ITree Require Export Traces Eq.
Require Import String. 


(* TODO: Use ITree library's ITreeNotations once conflicts with VST notation
   are resolved. *)
Module ITreeNotations.
(* Sometimes it's more convenient to work without the type classes
   Monad, etc. When functions using type classes are specialized,
   they simplify easily, so lemmas without classes are easier
   to apply than lemmas with.

   We can also make ExtLib's [bind] opaque, in which case it still
   doesn't hurt to have these notations around.
 *)

Notation "t1 >>= k2" := (ITree.bind t1 k2)
  (at level 50, left associativity) : itree_scope.
Notation "x <- t1 ;; t2" := (ITree.bind t1 (fun x => t2))
  (at level 100, t1 at next level, right associativity) : itree_scope.
Notation "t1 ;; t2" := (ITree.bind t1 (fun _ => t2))
  (at level 100, right associativity) : itree_scope.
Notation "' p <- t1 ;; t2" :=
  (ITree.bind t1 (fun x_ => match x_ with p => t2 end))
    (at level 100, t1 at next level, p pattern, right associativity) : itree_scope.

(* Infix ">=>" := ITree.cat (at level 50, left associativity) : itree_scope. *)

End ITreeNotations.

Import List.
Import ListNotations.

Export ITreeNotations.
Open Scope itree_scope.

Inductive is_vis_trace {InvisE VisE : Type -> Type} {R : Type}:
  itree (InvisE +' VisE) R -> @trace VisE R -> Prop  :=
| Trace_Empty (t : itree (InvisE +' VisE) R):
    is_vis_trace t (TEnd : trace)
| Trace_Ret (r : R): is_vis_trace (ret r) (TRet r)
| Trace_Tau (t : itree (InvisE +' VisE) R) (l : trace):
    is_vis_trace t l -> is_vis_trace (Tau t) l
| Trace_Invis (X : Type) (e : InvisE X) (k : X -> itree (InvisE +' VisE) R)
              (x : X) (l : trace):
    is_vis_trace (k x) l ->
    is_vis_trace (Vis (inl1 e) k) l
| Trace_Vis (X : Type) (f : VisE X) (k : X -> itree (InvisE +' VisE) R)
            (x : X) (l : trace):
    is_vis_trace (k x) l ->
    is_vis_trace (Vis (inr1 f) k) (TEventResponse f x l).

Definition vis_trace_incl
           {E F : Type -> Type} {R : Type}
           (t1 t2 : itree (E +' F) R) :=
  forall (tr : trace),
    is_vis_trace t1 tr -> is_vis_trace t2 tr.

Lemma vis_trace_incl_bind_assoc
      {E F : Type -> Type} {X Y Z}
      (m : itree (E +' F) X)
      (f : X -> itree (E +' F) Y)
      (g : Y -> itree (E +' F) Z)
      (t : itree (E +' F) Z) :
  vis_trace_incl (b <- (a <- m ;; f a) ;; g b) t ->
  vis_trace_incl (a <- m ;; b <- f a ;; g b) t.
Proof.
  admit.
Admitted.

Lemma vis_trace_or_incl_bind1
      {E: Type -> Type}
      {F : Type -> Type}
      `{nondetE -< E}
      {X Y}
      (m1 m2 : itree (E +' F) X) (k : X -> itree (E +' F) Y) :
  vis_trace_incl (x <- m1 ;; k x)
                 (x <- or m1 m2;; k x).
Proof.
  admit.
Admitted.

Lemma vis_trace_or_incl_bind2
      {E: Type -> Type}
      {F : Type -> Type}
      `{nondetE -< E}
      {X Y}
      (m1 m2 : itree (E +' F) X) (k : X -> itree (E +' F) Y) :
  vis_trace_incl (x <- m2 ;; k x)
                 (x <- or m1 m2;; k x).
Proof.
  admit.
Admitted.

Lemma vis_trace_incl_refl {E F : Type -> Type} {R}
      (m : itree (E +' F) R) : vis_trace_incl m m.
Proof.
  unfold vis_trace_incl.
  auto.
Qed.

Lemma vis_trace_or_incl
      {E F : Type -> Type}
      `{nondetE -< E}
      {R}
      (k1 k2 : itree (E +' F) R) :
  vis_trace_incl k1 (or k1 k2) /\ vis_trace_incl k2 (or k1 k2).
Proof.
  admit.
Admitted.

Definition vis_trace_eq {E F : Type -> Type} {R : Type}
           (m m' : itree (E +' F) R) : Prop :=
  forall t, is_vis_trace m t <-> is_vis_trace m' t.

Infix "≈" := (eutt eq) (at level 70) : itree_scope.

Lemma eutt_vis_trace {E F : Type -> Type} {R : Type}:
  forall (t1 t2 : itree (E +' F) R), t1 ≈ t2 -> vis_trace_eq t1 t2.
Proof.
  intros t1 t2 Heutt.
  intros t.
  induction t.
Admitted.

Fixpoint select' {X : Type}
         (pre xs : list X) {struct xs} : list (X * list X) :=
  match xs with
  | [] => []
  | x :: xs' => (x, pre ++ xs') :: select' (pre ++ [x]) xs'
  end.

Definition select {X : Type} : list X -> list (X * list X) := select' [].

Lemma select_select' {X : Type} (pre : list X) (l : list X):
  map (fun '(x, xs) => (x, pre ++ xs)) (select l) = select' pre l.
Proof.
  revert pre.
  induction l; intros pre; auto.
  simpl select'.
  unfold select.
  simpl.
  f_equal.
  rewrite <- (IHl (pre ++ [a])).
  rewrite <- IHl.
  rewrite map_map.
  f_equal.
  apply functional_extensionality.
  intros [x xs].
  rewrite app_assoc.
  reflexivity.
Qed.

Lemma select_sound' {X: Type} (pre : list X) (l : list X):
  forall x xs,
    In (x, xs) (select' pre l) ->
    (forall y : X, In y (x :: xs) <-> In y (pre ++ l)).
Proof.
  revert pre.
  induction l as [| a l]; intros pre x xs Hselect y.
  { split; intros Hy.
    - simpl in Hselect; contradiction.
    - simpl in Hselect; contradiction.
  }

  split.
  {
    intros Hy.
    simpl in Hselect.
    destruct Hselect as [H | H].
    - inversion H as [[x_eq xs_eq]]; subst x; rewrite <- xs_eq in *.
      simpl in Hy.
      apply in_or_app.
      simpl.
      destruct Hy as [| y_in]; auto.
      apply in_app_or in y_in.
      destruct y_in; auto.
    - apply IHl with (y := y) in H; auto.
      rewrite <- app_assoc in H.
      simpl in H.
      apply H.
      assumption.
  }

  {
    intros Hy.
    simpl in Hselect.
    destruct Hselect as [H | H].
    - inversion H as [[x_eq xs_eq]]; subst x; rewrite <- xs_eq in *.
      simpl.
      apply in_app_or in Hy.
      destruct Hy as [| Hy ].
      + right; apply in_or_app; left; trivial.
      + simpl in Hy.
        destruct Hy;
          [left; trivial | right; apply in_or_app; right; trivial].
    - rewrite IHl; eauto.
      rewrite <- app_assoc.
      trivial.

  }
Qed.


Lemma select_sound {X: Type} (l : list X):
  forall x xs,
    In (x, xs) (select l) ->
    (forall y : X, In y (x :: xs) <-> In y l).
Proof.
  intros.
  replace l with ([] ++ l) by reflexivity.
  eapply select_sound'; eauto.
Qed.

Lemma select_complete {X: Type} (l : list X):
  forall x, In x l ->
       (exists xs : list X, In (x, xs) (select l)).
Proof.
  intros x.
  induction l; intros HIn.
  { simpl in HIn; contradiction. }
  simpl in HIn.
  destruct HIn.
  - subst a.
    exists l.
    simpl; auto.
  - apply IHl in H.
    destruct H as [xs H].
    exists (a :: xs).
    simpl.
    right.
    rewrite <- select_select'.
    simpl.
    change (x, a :: xs)
             with ((fun '(x0, xs0) => (x0, a :: xs0)) (x, xs)).
    apply in_map.
    assumption.
Qed.

Definition failureE := exceptE string.

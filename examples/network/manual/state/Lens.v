From Coq
     Require Import
     Program.Basics.

Set Bullet Behavior "Strict Subproofs".

Definition compose {a b c : Type} (f : b -> c) (g : a -> b) := fun x => f (g x).

(** This file implements a very simple lens library,
    the LensLaws module describes "very well-behaved"
    lenses.

    See the Examples module on how to use lenses with
    the convenient infix notation.
*)

Record Lens (s a : Type) : Type :=
  mk_lens {
    get : s -> a;
    set : a -> s -> s
  }.

Arguments mk_lens {_ _} _ _.
Arguments get {_ _} _ _.
Arguments set {_ _} _ _ _.

Definition lens_compose
           {s a u : Type}
           (l1 : Lens s a)
           (l2 : Lens a u)
  : Lens s u
  := {|
       get := (compose (get l2) (get l1));
       set := fun u s => set l1 (set l2 u (get l1 s)) s
    |}.

Definition flip_app {a b : Type}
           (v : a) (f : a -> b) : b :=
  f v.


Module LensLaws.
  Record GoodLens (s a : Type) :=
    mk_good_lens {
        lens :> Lens s a;
        good_lens_get_set: forall s a, get lens (set lens a s) = a;
        good_lens_set_get: forall s, (set lens (get lens s) s) = s;
        good_lens_set_set: forall s a a', set lens a' (set lens a s) = set lens a' s
      }.

  Arguments mk_good_lens {_ _} _ _ _ _.
  Arguments lens {_ _} _.
  Arguments good_lens_get_set {_ _} _.
  Arguments good_lens_set_get {_ _} _.
  Arguments good_lens_set_set {_ _ } _.

  Definition good_lens_compose
             {s a u : Type}
             (l1 : GoodLens s a)
             (l2 : GoodLens a u)
    : GoodLens s u.
  Proof.
    destruct l1 as [l1' l1_get_set l1_set_get l1_set_set];
      destruct l2 as [l2' l2_get_set l2_set_get l2_set_set].
    refine(mk_good_lens (lens_compose l1' l2') _ _ _).
    - intros s_v a_v.
      simpl.
      unfold compose.
      rewrite l1_get_set.
      rewrite l2_get_set.
      auto.
    - intros s_v.
      simpl.
      unfold compose.
      rewrite l2_set_get.
      rewrite l1_set_get.
      auto.
    - intros s_v a_v a_v'.
      simpl.
      rewrite l1_get_set.
      rewrite l2_set_set.
      auto.
  Defined.

  Definition build_good_lens
             {s a: Type} (f : s -> a) (g : a -> s -> s) pf1 pf2 pf3 :=
    mk_good_lens (mk_lens f g) pf1 pf2 pf3.

  Ltac solve_set_get_destruct :=
    let x := fresh "x" in
    let Hx := fresh "H" x in
    intros x; destruct x eqn:Hx; reflexivity.

End LensLaws.

Module LensNotation.
  Import LensLaws.

  Infix ":&"  := flip_app     (at level 66, left associativity) : lens_scope.
  Infix ":∘"  := good_lens_compose (at level 64, left associativity) : lens_scope.
  Infix ":~" := set           (at level 65, no associativity) : lens_scope.
  Infix ":^" := (flip get)    (at level 65, no associativity) : lens_scope.

  Bind Scope lens_scope with Lens.
  Delimit Scope lens_scope with Lens.
  Delimit Scope lens_scope with lens.
End LensNotation.

Module Example.
  Import LensNotation.
  Import LensLaws.

  Record Bar := mk_bar {
                 b_num  : nat;
                 b_bool : bool
               }.

  Definition _b_num : GoodLens Bar nat.
  Proof.
    refine(
        build_good_lens b_num (fun n bar => mk_bar n (b_bool bar)) _ _ _
      ); auto.
    - solve_set_get_destruct.
  Defined.

  Definition _b_bool : GoodLens Bar bool.
  Proof.
    refine(
        build_good_lens b_bool (fun b bar => mk_bar (b_num bar) b) _ _ _
      ); auto.
    - solve_set_get_destruct.
  Defined.

  Record Foo := mk_foo {
                    f_bar : Bar;
                    f_num : nat
                  }.

  Definition _f_bar : GoodLens Foo Bar.
  Proof.
    refine (build_good_lens f_bar (fun bar foo => mk_foo bar (f_num foo)) _ _ _); auto.
    - solve_set_get_destruct.
  Defined.

  Definition _f_num : GoodLens Foo nat.
  Proof.
    refine (build_good_lens f_num (fun num foo => mk_foo (f_bar foo) num) _ _ _); auto.
    - solve_set_get_destruct.
  Defined.

  Example b := mk_bar 1 true.
  Example f := mk_foo b 10.

  (* accessing a nested value *)

  Import LensNotation.
  
  Eval compute in (f :^ (_f_bar :∘ _b_num))%lens.

  (* modifying a nested value *)
  Eval compute in ((f :&  (_f_bar :∘ _b_num :~ 100))
                      :&  (_f_num :~ 1000)
                  )%lens.
End Example.

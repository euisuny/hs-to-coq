From Coq Require Export List.
Export ListNotations.

Fixpoint take_while {A} (f : A -> bool) (xs : list A) : list A :=
  match xs with
  | [] => []
  | x :: xs =>
    if f x then
      x :: take_while f xs
    else
      []
  end.

(* Helper for [picks]. *)
Fixpoint picks' {A} (xs1 xs2 : list A) : list (A * list A) :=
  match xs2 with
  | [] => []
  | x2 :: xs2' =>
    (x2, rev_append xs1 xs2') :: picks' (x2 :: xs1) xs2'
  end.

(* List of ways to pick an element out of a list. *)
Definition picks {A} (xs : list A) : list (A * list A) :=
  picks' [] xs.

Example picks_example : picks [1;2] = [(1,[2]); (2,[1])].
Proof. reflexivity. Qed.

Fixpoint filter_opt {A B} (f : A -> option B) (xs : list A) : list B :=
  match xs with
  | [] => []
  | x :: xs =>
    match f x with
    | Some y => y :: filter_opt f xs
    | None => filter_opt f xs
    end
  end.

Fixpoint find_opt {A B} (f : A -> option B) (xs : list A) : option B :=
  match xs with
  | [] => None
  | x :: xs =>
    match f x with
    | Some y => Some y
    | None => find_opt f xs
    end
  end.

Definition replace_when {A : Type} (f : A -> bool) (new : A) (l : list A) :=
  List.fold_right
    (fun a tail => (if f a then new else a) :: tail)
    [] l.

Lemma In_replace_when {A : Type} f l (new x : A) :
  In x (replace_when f new l) -> new = x \/ (f x = false /\ In x l).
Proof.
  induction l.
  - intros [].
  - intros [Ha | Hl].
    + destruct (f a) eqn:Hf.
      * auto.
      * right. subst a. split; auto. left; auto.
    + destruct (IHl Hl).
      * auto.
      * right. split. { apply H. } { right. apply H. }
Qed.

Lemma In_replace_when2 {A : Type} f l (new x : A) :
  In x (replace_when f new l) ->
  (exists old, In old l /\ f old = true /\ new = x)
  \/ (f x = false /\ In x l).
Proof.
  induction l; [intros [] | ].
  intros [Ha | Hl].
  - destruct (f a) eqn:Hf.
    + left. exists a; split; simpl; auto.
    + right. subst a. split; auto. left; auto.
  - destruct (IHl Hl) as [[old [old_in H]] | Hright].
    + left; eexists; split; auto.
      simpl.
      * right; eassumption.
      * assumption.
    + right; intuition. 
Qed.

Lemma map_replace_when {A B : Type} (f : A -> B) (p : A -> bool)
      l new :
  (forall x, p x = true -> f x = f new) ->
  map f (replace_when p new l) = map f l.
Proof.
  intros Hpf.
  induction l; auto.
  simpl.
  destruct (p a) eqn:pa_bool.
  - rewrite <- (Hpf a pa_bool); f_equal; apply IHl.
  - f_equal; apply IHl.
Qed.

Lemma filter_app: forall {A : Type} f (l1 l2 : list A),
  filter f (l1 ++ l2) = filter f l1 ++ filter f l2.
Proof.
  induction l1; intros; trivial.
  simpl.
  destruct (f a); trivial.
  simpl.
  f_equal.
  apply IHl1.
Qed.

Lemma filter_incl:
  forall {A} (p : A -> bool) l, incl (filter p l) l.
Proof.
  unfold incl.
  intros ? ? ? ? HIn.
  rewrite filter_In in HIn.
  destruct HIn; assumption.
Qed.

Lemma same_key_preserves_NoDup:
  forall (T U : Type) (g : T -> U) (t t' : T) (prefix suffix : list T),
    g t = g t' ->
    NoDup (map g (prefix ++ t :: suffix)) ->
    NoDup (map g (prefix ++ t' :: suffix)).
Proof.
  intros T U g t t' prefix suffix Heq HNoDup.
  rewrite map_app in *.
  simpl in *.
  rewrite <- Heq.
  trivial.
Qed.

Lemma conditional_bool : forall (b : bool) c,
    (if b then c else false) = true <-> c = true /\ b = true.
Proof.
  intros [] c; intuition.
Qed.

Lemma conditional_dec_true : forall (P : Prop) (b : {P} + {~P}),
    (if b then true else false) = true <-> P.
Proof.
  intros P []; intuition.
  discriminate.
Qed.

(**)

Definition prefix {A : Type} (p l : list A) := exists q, l = p ++ q.

Lemma firstn_prefix : forall A n (s : list A),
    prefix (firstn n s) s.
Proof.
  induction n; intro s.
  - exists s. auto.
  - destruct s; simpl.
    exists []; auto.
    destruct (IHn s) as [q Hq].
    exists q.
    simpl; rewrite <- Hq; auto.
Qed.

(**)

Lemma skipn_all {A : Type} (len : nat) (xs : list A) :
  len = length xs -> skipn len xs = [].
Proof.
  intros H; subst len.
  induction xs; simpl; auto.
Qed.

Lemma skipn_length {A : Type} (n : nat) : forall xs : list A,
  length (skipn n xs) = length xs - n.
Proof.
  induction n; destruct xs; simpl; auto.
Qed.

Lemma skipn_skipn {A: Type} (xs : list A): forall (n m : nat),
    skipn n (skipn m xs) = skipn (n + m) xs.
Proof.
  induction xs; intros n m; [destruct n, m; auto |].
  destruct m.
  - simpl. rewrite Plus.plus_0_r. reflexivity.
  - simpl.
    rewrite <- Plus.plus_Snm_nSm.
    simpl.
    apply IHxs.
Qed.
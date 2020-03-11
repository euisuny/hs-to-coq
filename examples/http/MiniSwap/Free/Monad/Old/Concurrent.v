Require String.

From QuickChick Require Show.

From DeepWeb.Free.Monad Require Import
     Free Common Eq.Eq.
Import MonadNotations.

(* [interleave f spin y = interleave f x spin = spin]
   (i.e., [spin] starves the other thread).
   This is not so bad when the spec is not supposed to
   spin. *)
CoFixpoint interleave {E X Y Z} `{nondetE -< E}
           (f : X -> Y -> Z)
           (p1 : itree E X) (p2 : itree E Y)
  : itree E Z :=
  match p1, p2 with
  | Ret x, _ => y <- p2 ;; ret (f x y)
  | _, Ret y => x <- p1 ;; ret (f x y)
  | Tau p1', _ => Tau (interleave f p1' p2)
  | _, Tau p2' => Tau (interleave f p1 p2')
  | Vis e1 k1, Vis e2 k2 =>
    or (Vis e1 (fun z1 => interleave f (k1 z1) p2))
       (Vis e2 (fun z2 => interleave f p1 (k2 z2)))
  end.

Module Export Atomic.

Inductive atomE E X : Type :=
| Atom : itree E X -> atomE E X.

Arguments Atom {E X}.

Definition atomically {E X} (m : itree E X) : itree (atomE E) X :=
  liftE (Atom m).

Definition fission {E X} (a : atomE E X) : itree E X :=
  match a with
  | Atom m => m
  end.

Section Instances.

Import String.
Import Show.
Open Scope string.

Global Instance Show_atomE E X `{Show (itree E X)} : Show (atomE E X) :=
  { show a := match a with
              | Atom m => "Atom (" ++ show m ++ ")"
              end
  }.

End Instances.
End Atomic.

Ltac step :=
  match goal with
  | [ |- eq_itree ?m ?n ] =>
    rewrite (match_itree m);
    rewrite (match_itree n)
  end.

Lemma interleave_left_zero {E X Y Z} `{nondetE -< E}
      (f : X -> Y -> Z)
  : forall p2, (interleave f spin p2 = spin)%eq_itree.
Proof.
  cofix self.
  intros.
  step.
  destruct p2; simpl; constructor.
  - (* Proof by hand that [spin >>= _ = spin] *)
    cofix self_spin; step; constructor; auto.
  - apply self.
  - apply self.
Qed.

Lemma interleave_right_zero {E X Y Z} `{nondetE -< E}
      (f : X -> Y -> Z)
  : forall p1, (interleave f p1 spin = spin)%eq_itree.
Proof.
  cofix self.
  intros.
  step.
  destruct p1; simpl; constructor.
  - cofix self_spin; step; constructor; auto.
  - apply self.
  - apply self.
Qed.

(* TODO *)
(* ... Maybe we can test these? *)
(* Note: generating infinite structures is nicer with
   splittable PRNGs. *)

Lemma interleave_comm {E X Y Z} `{nondetE -< E} (f : X -> Y -> Z)
  : forall p1 p2,
    interleave f p1 p2
    = (* for some alternative definition of [=] *)
    interleave (fun y x => f x y) p2 p1.
Proof.
Abort.

Lemma interleave_assoc {E X Y Z XY XYZ} `{nondetE -< E}
      (f : X -> Y -> XY) (g : XY -> Z -> XYZ)
  : forall (p1 : itree E X) p2 p3,
    interleave g (interleave f p1 p2) p3
    = (* for some alternative definition of [=] *)
    interleave (fun x h => h x)
               p1
               (interleave (fun y z x => g (f x y) z) p2 p3).
Proof.
Abort.

Lemma interleave_left_id {E X Y Z} `{nondetE -< E}
      (f : X -> Y -> Z)
  : forall x p2,
    interleave f (Ret x) p2
    =
    map_itree (f x) p2.
Proof.
Abort.

Lemma interleave_right_id {E X Y Z} `{nondetE -< E}
      (f : X -> Y -> Z)
  : forall p1 y,
    interleave f p1 (Ret y)
    =
    map_itree (fun x => f x y) p1.
Proof.
  (* by commutativity and left-identity *)
Abort.

Module InterleaveMore.
(* Variants of [interleave] *)

(* Here's a helper function that finds the first non-Tau
   constructor. *)
Definition make_progress {E F X Y}
           `(on_Ret : X -> itree F Y)
           `(on_Vis : forall Z, E Z -> (Z -> itree E X) -> itree F Y)
  : itree E X -> itree F Y :=
  cofix make_progress' p :=
    match p with
    | Ret x => on_Ret x
    | Vis e k => on_Vis _ e k
    | Tau p' => Tau (make_progress' p')
    end.

(* We can use it to write this function that should be
   equivalent to [interleave] above.
   This refactoring doesn't seem like a win... *)
CoFixpoint interleave_bis {E X Y Z} `{nondetE -< E}
           `(f : X -> Y -> Z)
           (p1 : itree E X) (p2 : itree E Y)
  : itree E Z :=
  make_progress
    (fun x => y <- p2;; ret (f x y))
    (fun _ e1 k1 =>
       make_progress
         (fun y => Vis e1 (fun z => x <- k1 z;; ret (f x y)))
         (fun _ e2 k2 =>
            or (Vis e1 (fun z => interleave_bis f (k1 z) (Vis e2 k2)))
               (Vis e2 (fun z => interleave_bis f (Vis e1 k1) (k2 z))))
         p2)
    p1.

(* [interleave_fair x (Vis e ?) = or ? (Vis e ?)]
   (i.e., there is visible progress.)
 *)
CoFixpoint interleave_fair {E X Y Z} `{nondetE -< E}
           `(f : X -> Y -> Z)
           (p1 : itree E X) (p2 : itree E Y)
  : itree E Z :=
  or (interleave_progress f p1 p2)
     (interleave_progress (fun y x => f x y) p2 p1)

with
interleave_progress {E X Y Z}
  `{nondetE -< E}
  `(f : X -> Y -> Z)
  (p1 : itree E X) (p2 : itree E Y)
: itree E Z :=
  make_progress
    (fun x => y <- p2;; ret (f x y))
    (fun _ e k => Vis e (fun z => interleave_fair f (k z) p2))
    p1.

Lemma interleave_fair_left_spin {E Y} `{nondetE -< E}
  : forall `(p2 : itree E Y),
    interleave_fair (fun v _ => match v : void with end) spin p2
    = (* Some (non-equivalence?) relation... *)
    p2.
Proof.
Abort.

(* Also the usual, associativity, commutativity, identity *)

(* Another one would be to branch after every constructor,
   but that would be very redundant and slow to search during
   testing. *)

End InterleaveMore.

(*
Inductive ForkJoin (E : Type -> Type) : Type -> Type :=
| Fork : forall X Y, ForkJoin E X -> ForkJoin E Y -> ForkJoin E (X * Y)
| Join : forall X, itree E X -> ForkJoin E X.

Notation Conc Event := (ForkJoin (nondetE + Event) + (nondetE + Event)).
 *)

(*
Inductive Fork (E : Type -> Type) : Type -> Type :=
| ForkJoin : forall X Y, itree (Fork E + E) X -> itree (Fork E + E) Y
                         -> Fork E (X * Y).

Notation Conc Event := (Fork Event + Event).
 *)

(*
Fixpoint step E X
          (p : ForkJoin E X)
  : itree (nondetE + E) (ForkJoin E X + X) :=
  match p with
  | Join m =>
    match m with
    | Ret x => ret (inr x)
    | Tau n => Tau (ret (inl (Join n)))
    | Vis e h => Vis (RightE e) (fun x => ret (inl (Join (h x))))
    end
  | Fork p1 p2 =>
    Vis (LeftE Or)
        (fun b =>
           if b then
             step p1
        )
  end.





CoFixpoint runCont E X (m : itree (Conc (nondetE + E) + nondetE + E) X)
  : itree (nondetE + E) X :=
  match m with
  | Ret x => Ret x
  | Tau n => Tau (runCont n)
  | Vis e k =>
    match e with
    | LeftE (LeftE (ForkJoin p1 p2)) =>
      match p1, p2 with
      | Ret x, Ret y => k (x, y)
      | _, _ =>
        Vis (LeftE (RightE Or))
            (fun b =>
               if b then
                 
    end
  end.
*)

From DeepWeb.Free Require Import
     Free.

(* If we can interpret the events of one such monad as computations in
    another, we can extend that interpretation to the whole monad. *)

Notation "E ~> F" := (forall X, E X -> F X) (at level 95).

Definition hom_body
           {E1 E2 : Type -> Type}
           (f : forall X, E1 X -> itree E2 X)
           (R : Type)
           (hom_ : itree E1 R -> itree E2 R) :
  itree E1 R -> itree E2 R :=
  fun p =>
    match p with
    | Ret x => Ret x
    | Vis e k => bind_itree (f _ e) (fun x => hom_ (k x))
    | Tau k => Tau (hom_ k)
    end.

Definition hom
           {E1 E2 : Type -> Type}
           (f : forall X, E1 X -> itree E2 X)
           (R : Type) :
  itree E1 R -> itree E2 R :=
  cofix hom_ (p : itree E1 R) : itree E2 R :=
    hom_body f _ hom_ p.

Definition hom_state
           {E1 E2 : Type -> Type}
           {S : Type}
           (f : forall X, S -> E1 X -> itree E2 (S * X))
           (R : Type) :
  S -> itree E1 R -> itree E2 (S * R) :=
  cofix hom_ s (p : itree E1 R) : itree E2 (S * R) :=
    match p with
    | Ret x => Ret (s, x)
    | Vis e k => bind_itree (f _ s e) (fun sa => hom_ (fst sa) (k (snd sa)))
    | Tau k => Tau (hom_ s k)
    end.

Lemma hom_def {E1 E2 R} (f : E1 ~> itree E2) (p : itree E1 R) :
  hom f _ p = hom_body f _ (hom f _) p.
Proof.
  rewrite (match_itree (hom _ _ _)).
  rewrite (match_itree (hom_body _ _ _ _)).
  reflexivity.
Qed.

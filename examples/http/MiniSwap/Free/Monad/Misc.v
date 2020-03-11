
Definition fold_finite {E X R}
           (default : R)
           (ret_ : X -> R)
           (f : forall X, E X -> (X -> R) -> R) : nat -> itree E X -> R :=
  fix fold_ max_depth t :=
    match max_depth with
    | O => default
    | S max_depth =>
      match t with
      | Ret x => ret_ x
      | Tau t => fold_ max_depth t
      | Vis e k => f _ e (fun x => fold_ max_depth (k x))
      end
    end.

Fixpoint collapse_root {E X} (fuel : nat) (m : itree E X) : itree E X :=
  match fuel with
  | O => m
  | S fuel' =>
    match m with
    | Tau m' => collapse_root fuel' m'
    | _ => m
    end
  end.

CoFixpoint collapse {E X} (refuel : nat) (m : itree E X) : itree E X :=
  match collapse_root refuel m with
  | Tau m' => Tau (collapse refuel m')
  | Vis e k => Vis e (fun z => collapse refuel (k z))
  | Ret x => Ret x
  end.

(* ------------------------------------------------------------- *)

Module MORE.

(* Some more interesting algebraic structure.  This is not immediately
   useful for zipping tests and programs because there are things in
   tests that we do not want to zip with anything in the program.
   Might be useful later for something, though. *)

Inductive Pair1 (E1 E2: Type -> Type) : Type -> Type :=
 | pair1 {X} {Y} (e1 : E1 X) (e2 : E2 Y) : Pair1 E1 E2 (X * Y).

(* If we can interpret two infinite streams with different events as
   one where we line up the events in lockstep. *)
Definition lockstep {E1 E2 : Type -> Type} {X} : itree E1 X -> itree E2 X -> itree (Pair1 E1 E2) X :=
  cofix go p1 p2 :=
    match p1, p2 with
      | Tau p1', _ => Tau (go p1' p2)
      | _, Tau p2' => Tau (go p1 p2')
      | Ret x,_ => Ret x
      | _, Ret x => Ret x
      | Vis e1 p1k, Vis e2 p2k =>
        Vis (pair1 e1 e2) (fun p => match p with (x, y) => go (p1k x) (p2k y) end)
    end.
(* There are a few variants depending on which return values we want
   to to force to be void. But this seems to be the most general
   one.*)

End MORE.

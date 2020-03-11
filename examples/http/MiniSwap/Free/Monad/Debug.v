From DeepWeb.Free.Monad Require Import
     Free.

Inductive _M {E R} (n : nat) : itree E R -> Prop :=
| MTau : forall t, _M (S n) t -> _M n (Tau t)
| MVis : forall X (e : E X) k x, _M (S n) (k x) -> _M n (Vis e k).

Ltac simpl_M := rewrite match_itree; simpl; try rewrite <- match_itree.
Ltac step_tau := repeat (apply MTau; simpl_M).
Tactic Notation "step" uconstr(y) := (eapply MVis with (x := y); simpl_M; step_tau).

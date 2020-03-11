From Coq Require Import String.
From QuickChick Require Import QuickChick.
From ExtLib Require Import Monads.

Inductive optionE (X:Type) : Type :=
  | Success : X -> optionE X
  | Failure : string -> optionE X.

Arguments Success {X}.
Arguments Failure {X}.

Instance Monad_optionE : Monad optionE :=
  { ret A x := Success x;
    bind A B a f := match a with
                    | Success a' => f a'
                    | Failure e => Failure e
                    end }.

Instance Exception_optionE : MonadExc string (optionE) :=
  { raise A x := Failure x;
    catch A e f := match e with
                   | Failure e => f e
                   | a => a
                   end }.

Generalizable Variable X.
Instance show_optionE `{Show X} : Show (optionE X) :=
  { show e := match e with
              | Failure err => "(Failure) " ++ err
              | Success v => "(Success) " ++ show v
              end%string
  }.

Coercion toOption {X} (x : optionE X) : option X :=
  match x with
  | Success x' => Some x'
  | Failure _ => None
  end.

Global Instance Dec_eq_optionE (A : Type) (m n : optionE A)
         `{_ : forall (x y : A), Dec (x = y)} : Dec (m = n).
Proof. dec_eq. Defined.

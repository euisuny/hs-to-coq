(** * Linear specification of hello server *)

(* The effect type [specE] used by the specification is defined
   in [SpecEffect] as

       Definition specE := failureE +' nondetE +' observerE.

   where [observerE] is defined there, [failureE] and [nondetE]
   are general-purpose exception and nondeterminism effects from
   the InteractionTree library.
 *)

From ITree Require Import
     ITree
     Events.Nondeterminism.

From Coq Require Import
     Ascii String List PArith ZArith.
From Coq Require Fin.

From QuickChick Require Import QuickChick.
From ExtLib Require Import Monad.
Open Scope monad_scope.
Require Import ServerDefs StringLib SpecEffect.
Import ListNotations MonadNotation.

(* begin hide *)
Set Warnings "-extraction-opaque-accessed,-extraction".
(* end hide *)

Section LinearSpec.
Variable (app : App.t).

(* ====================================================== *)
(** *Linear Specification *)
(* ====================================================== *)
CoFixpoint linear_spec'
           (conns : list connection_id)
           (s : App.state app)
  : itree specE unit :=
    or ( (* Accept a new connection. *)
      c <- obs_connect;;
      linear_spec' (c :: conns) s
    )
    ( (* Send Hello World message from server. *)
      c <- choose conns;;
      let '(s', resp) := App.app app s in
      obs_msg_from_server c resp;;
      linear_spec' conns s'
    ).

(* Top-level spec. *)
Definition linear_spec :=
  linear_spec' [] (App.initial_state app).

End LinearSpec.

Definition hello_app_spec := linear_spec hello_app.

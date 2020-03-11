Require Import DeepWeb.Free.Monad.Free.

(*! Section ImplModelTest *)(*! extends BaseTest *)

(* Simulate a server (defined in Coq, hence "internal"),
   nondeterministically returning the new state of the network. *)

Typeclasses eauto := 6.

From QuickChick Require Import QuickChick.
From ExtLib Require Monad.

From DeepWeb Require Import
     Lib.LinearSpec_Core.

Import LinearSpec_Server.

From DeepWeb.Spec Require
     Swap_ImplModel
     Swap_LinearSpec.

Definition swap_server : itree implE unit :=
  Swap_ImplModel.test_swap_impl'.
Definition swap_observer : itree specE unit :=
  Swap_LinearSpec.test_swap_spec.

Definition test : Checker :=
  network_refines_test
    swap_observer
    swap_server.

(*! QuickChick test. *)

(* NOT USED -- random_trace is only used here for debugging
    (* Enumerate the traces of the [server'] itree (swap server). *)
    Definition random_trace_server :=
      random_trace 500 10 swap_server.

    (* Sample random_trace_server. *)
*)


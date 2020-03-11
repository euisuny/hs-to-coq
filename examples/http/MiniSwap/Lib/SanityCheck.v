(* Check that the interfaces defined in [Lib.LinearSpec_Interface]
   are actually implemented by the modules actually
   exported by [Lib.LinearSpec]. *)

From DeepWeb.Free.Monad Require Import
     Free Common.
Import SumNotations.

Require Import DeepWeb.Lib.Util.

From DeepWeb Require Import
     Lib.LinearSpec
     Lib.LinearSpec_Interface.

Module Server <: ServerIface.
Import LinearSpec_Server.
Include ServerType.
Definition implE := failureE +' nondetE +' serverE.
Definition accept := @accept implE _.
Definition recv_byte := @recv_byte implE _.
Definition send_byte := @send_byte implE _.
Definition recv := @recv implE _ _.
Definition recv_full := @recv_full implE _.
Definition send := @send implE _.
End Server.

Module Observer <: ObserverIface.
Include Lib.LinearSpec_Observer.ObserverType.
Definition specE := failureE +' nondetE +' observerE.
Definition obs_connect := @obs_connect specE _.
Definition obs_to_server := @obs_to_server specE _.
Definition obs_from_server := @obs_from_server specE _.
Definition assert_on A := @assert_on specE A _ _.
Definition obs_msg_to_server := @obs_msg_to_server specE _.
Definition obs_msg_from_server := @obs_msg_from_server specE _ _ _.
End Observer.

Module Traces <: TracesIface Server Observer.
  Include LinearSpec_Traces.
  Definition is_impl_trace := LinearSpec_Server.is_impl_trace.
  Definition is_spec_trace := LinearSpec_Observer.is_spec_trace.
  Definition is_spec_trace_test := LinearSpec_Observer.is_spec_trace_test.
End Traces.

Module NetworkModel <: NetworkModelIface.
  Include LinearSpec_NetworkModel.
End NetworkModel.

Module Reordering
  <: ReorderingIface Server Observer Traces NetworkModel.
  Include Traces.

  Definition impl_behavior := LinearSpec_Server.impl_behavior.

  Definition spec_behavior := LinearSpec_Observer.spec_behavior.

  Definition network_refines
    := LinearSpec.Refinement.network_refines.

  Definition reordered_result := Lib.Util.result hypo_trace unit.
  Definition is_disordered_trace_test
    := LinearSpec_Descramble.is_disordered_trace_test.
  Definition network_refines_test
    := LinearSpec_ServerTrace.network_refines_test.
End Reordering.

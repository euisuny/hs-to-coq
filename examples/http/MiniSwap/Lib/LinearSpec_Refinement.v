Require Import Relations.
Require Import RelationClasses.

From QuickChick Require Import QuickChick.
From Custom Require Import List.
Import ListNotations.
From Custom Require Map.

Require Import DeepWeb.Free.Monad.Free.
Require Import DeepWeb.Free.Monad.Common.
Import SumNotations.

Require Import DeepWeb.Lib.Util.

From DeepWeb Require Import
     Lib.LinearSpec_NetworkModel
     Lib.LinearSpec_Server
     Lib.LinearSpec_Observer
     Lib.LinearSpec_Scramble
     Lib.LinearSpec_Traces.

Import LinearSpec_Server.

Set Bullet Behavior "Strict Subproofs".

(* The definition of "refinement" between an itree representing
   a server implementation, and an itree of "linear traces"
   as a specification. The [ScramblingFacts] that the
   theorems below depend on are defined and proved in
   [Lib.LinearSpec_Scramble]. *)

Module Refinement (ScramblingFacts : ScramblingTypes).
Import ScramblingFacts.

(* A server ([impl : itree implE unit]) refines a "linear spec"
   ([spec : itree specE unit]) if, for every trace [tr_impl] that
   the server can produce, and every trace [tr] that can be observed
   from it via the network (i.e., a client-side reordering of
   [tr_impl]), it can be explained by a server-sider reordering
   of the "linear spec" [spec].
   Some examples can be found in [Spec.Scramble_Examples].
 *)
Definition network_refines impl spec : Prop :=
  forall tr,
    impl_behavior impl tr -> spec_behavior spec tr.

(* It turns out that we can simplify this property to remove an
   intermediate step.
   It is sufficient to reorder only the traces of the
   implementation directly to traces of the linear spec.
   In fact, [network_refines_equiv] shown below establishes
   the equivalence between these two properties. *)
Definition strong_network_refines impl spec : Prop :=
  forall tr_impl : real_trace,
    wf_trace tr_impl ->
    is_impl_trace impl tr_impl ->
      exists tr_spec : real_trace,
        network_reordered tr_spec tr_impl /\
        is_spec_trace spec tr_spec.

(* [strong_sound] and [strong_complete] rely on two properties
   of the [network_reordered] relation: it is reflexive
   ([reordered_reflexive]) and transitive ([reordered_transitive]).
   (These are shown in [Lib.LinearSpec_Scramble].)
 *)

Definition network_refines_equiv :
  forall impl spec,
    strong_network_refines impl spec <->
    network_refines impl spec.
Proof.
  intros server spec; split.
  - intros Hstrong str [tr [Htr_istrace Hstr_reordered]].
    pose proof (reordered_implies_wf _ _ Hstr_reordered) as Hwf.
    destruct (Hstrong tr (proj1 Hwf) Htr_istrace)
      as [dstr [Hdstr_reordered Hdstr_istrace]].
    exists dstr.
    split; auto.
    etransitivity; eauto.

  - intros Hcorrect tr Htr_wf Htr_istrace.
    unfold network_refines in Hcorrect.
    destruct (Hcorrect tr)
      as [dstr [Hdstr_reordered Hdstr_istrace]].
    { exists tr. split; auto.
      apply reordered_reflexive; auto. }
    exists dstr.
    auto.
Qed.

(* [network_refines] is part of the toplevel property
   about the swap server, stated in [Spec.TopLevelSpec]. *)

End Refinement.

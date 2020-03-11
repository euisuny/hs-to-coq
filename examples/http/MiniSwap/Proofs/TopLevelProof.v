From DeepWeb.Spec
     Require Import TopLevelProp Swap_ImplModel.

From DeepWeb.Proofs.Vst
     Require Import verif_prog.

From DeepWeb.Proofs.Linear Require
     Top.

Import ZArith.

Set Bullet Behavior "Strict Subproofs".

Theorem swap_server_is_correct : swap_server_correct.
Proof.
  unfold swap_server_correct.
  exists real_swap_impl.
  split.
  - pose proof (@Top.real_server_refines_swap) as H.
    apply (Top.real_server_refines_swap).
  - apply prog_correct.
Qed.

Require Import String.

From DeepWeb.Spec.Vst
     Require Import MainInit Gprog SocketSpecs.

From DeepWeb.Lib
     Require Import VstLib.

From DeepWeb.Proofs.Vst
     Require Import VerifLib SocketTactics.

Import FDSetPred.

Open Scope list.
Open Scope logic.

Set Bullet Behavior "Strict Subproofs".

Lemma body_add_to_fd_set:
  semax_body Vprog Gprog f_fd_zero_macro fd_zero_macro_spec.
Proof.
  start_function.
  
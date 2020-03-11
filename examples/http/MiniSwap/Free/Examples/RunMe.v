Require Import List.
Import ListNotations.
Require Import String.
Require Import QuickChick.QuickChick.
(* Require Import DeepWeb.Free.Examples. *)
Require Import DeepWeb.Free.SocketLoop.

Definition quickChick {prop : _} {_ : Checkable prop} (p : prop)
  : string :=
  show (quickCheckWith (updMaxSuccess stdArgs 1000) p).

Definition spec_out : string :=
  quickChick
    (* Examples.the_spec *)
    SocketLoop.TestSpec.good_test
    (* SocketLoop.TestSpec.imp_drop_send_test *)
    (* SocketLoop.TestSpec.imp_two_send_test *)
    (* SocketLoop.TestSpec.spec_drop_send_test *)
    (* SocketLoop.TestSpec.spec_two_send_test *)
.

(* Definition spec_out : string := show (SocketLoop.TestSpec.sampl__) *)

Separate Extraction spec_out.

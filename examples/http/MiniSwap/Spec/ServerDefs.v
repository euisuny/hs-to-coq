Require Import Coq.ZArith.ZArith.

From Custom Require Import String.
Require Import DeepWeb.Lib.Util.
Require Import DeepWeb.Lib.NetworkInterface.

Definition BUFFER_SIZE : Z := 1024.
Definition SERVER_PORT : endpoint_id := Endpoint 8000.

Definition INIT_MSG := repeat_string "0"%char (Z.to_nat BUFFER_SIZE).

Module App.
Record t : Type := {
  req_size : nat; (* May be replaced with a parser *)
  state : Type;
  initial_state : state;
  app : state * string -> state * string;
}.
End App.

Definition is_complete (app : App.t) (msg : string) :=
  (String.length msg =? App.req_size app)%nat.

Module SwapConfig.
Record t : Type := {
  req_size : nat;
  initial_state : string;
}.
End SwapConfig.

Section SwapApp.
Import App.

Definition swap_app (config : SwapConfig.t) : App.t := {|
  req_size := SwapConfig.req_size config;
  state := string;
  initial_state := SwapConfig.initial_state config;
  app := fun '(last_msg, new_msg) => (new_msg, last_msg);
|}.

Definition real_swap_config : SwapConfig.t := {|
  SwapConfig.req_size := Z.to_nat BUFFER_SIZE;
  SwapConfig.initial_state := INIT_MSG;
|}.

Definition real_swap_app := swap_app real_swap_config.

Definition test_swap_config : SwapConfig.t :=
  let sz := 3 in {|
  SwapConfig.req_size := sz;
  SwapConfig.initial_state := repeat_string "0"%char sz;
|}.

Definition test_swap_app := swap_app test_swap_config.

End SwapApp.

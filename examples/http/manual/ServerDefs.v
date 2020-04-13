(* ====================================================== *)
(** *Specification of simple server *)
(* ====================================================== *)
From ITree Require Import Traces.

Require Import Coq.ZArith.ZArith.
Require Import StringLib.

(* ====================================================== *)
(** *Modeling Network App State

    The network state contains information about the
    buffer size, initial state, and the state transitions
    that define the behavior of the application.
 *)
(* ====================================================== *)

(** *Sockets, Endpoints and Connection IDs

    A *socket* is one endpoint of a two-way communication
    link between two programs running on the network. A socket
    is bound to a port number so that the TCP layer can
    identify the application that data is destined to be sent to.

    From the standpoint of the network state (the oracle that
    we wish to specify), we do not care for the representation
    of sockets. Rather, we care about the state of the connection
    endpoints themselves.

    For BOUND and LISTENING sockets, we give `endpoint_ID`s,
    which correspond to sockets on the server side.

    CONNECTED sockets have `connection_id`s, which is assigned
    to clients.  

    CLOSED and OPENED sockets have no reperesntation in our
    network state oracle.
 *)

Inductive connection_id : Type := Connection (c : nat).
Record endpoint_id : Type := Endpoint { port_number : Z; }.

(* Assume buffer size to be 1024 bytes. *)
Definition BUFFER_SIZE : Z := 1024.
Definition SERVER_PORT : endpoint_id := Endpoint 4242.

Definition byte := Ascii.ascii.
Definition bytes := string.
Definition hello_message : bytes := "Hello, World!".

Definition
  INIT_MSG := hello_message ++ repeat_string "0"%char (Z.to_nat BUFFER_SIZE -
                                                       (length hello_message)).

Module App.
Record t : Type := {
  req_size : nat;
  state : Type;
  initial_state : state;
  app : state -> state * bytes;
}.
End App.

Module Config.
Record t : Type := {
  req_size : nat;
  initial_state : string;
}.
End Config.

Section HelloApp.
Import App.

(* Constant state: server always sends Hello World message *)
Definition network_app (config: Config.t): App.t :=
  {|
    req_size := Config.req_size config;
    state := string;
    initial_state := Config.initial_state config;
    app := fun 'state => (state, state);
  |}.

Definition hello_app_config : Config.t :=
  {|
    Config.req_size := Z.to_nat BUFFER_SIZE;
    Config.initial_state := INIT_MSG;
  |}.

Definition hello_app := network_app hello_app_config.

End HelloApp.

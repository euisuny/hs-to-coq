(* Overview of the main entities involved in our formalization of
   linearizability.
   This module contains only module types for documentation purposes.
 *)

Require Import List.
Import ListNotations.

From QuickChick Require Import QuickChick.
From Custom Require Import String Monad.
From Custom Require Map.
Import MonadNotations.

Require Import DeepWeb.Free.Monad.Free.
Require Import DeepWeb.Free.Monad.Common.
Import SumNotations.

Require Import DeepWeb.Lib.Util.

(** * Interfaces *)

(** ** Server *)

(* Types and operations for defining server implementation ITrees. *)
Module Type ServerIface.

(* A server is a program with internal nondeterminism and
   external network effects. *)
Inductive serverE : Type -> Type :=
  | (* Accept a new connection. *)
    Accept   : serverE connection_id
  | (* Receive one byte from a connection. *)
    RecvByte : connection_id -> serverE byte
  | (* Send one byte to a connection. *)
    SendByte : connection_id -> byte -> serverE unit.

(* The type of events that implementations are over. 
   A server is a program with internal nondeterminism and
   external network effects. *)
Definition implE := failureE +' nondetE +' serverE.

(* We wrap these constructors into [itree implE] values for convenience. *)

Definition accept :
  itree implE connection_id := embed Accept.
Definition recv_byte :
  connection_id -> itree implE byte := embed RecvByte.
Definition send_byte :
  connection_id -> byte -> itree implE unit := embed SendByte.

(* A few more useful operations, written using those above. *)

(* Receive up to [n] bytes, nondeterministically. *)
Parameter recv : connection_id -> nat -> itree implE bytes.

(* Receive a bytestring of length (exactly) [n]. *)
Parameter recv_full : connection_id -> nat -> itree implE bytes.

(* Send all bytes in a bytestring. *)
Parameter send : connection_id -> bytes -> itree implE unit.

End ServerIface.
(* Implemented in [Lib.LinearSpec_Server]. *)

(** ** Observer *)

(* Types and operations for defining specifications as "observer"
   ITrees. *)

Module Type ObserverIface.

(* The interface of observers is similar to servers; the difference is
   that observer ITrees only _consume_ bytes (the types of their
   events return bytes as outputs, rather than taking them as inputs),
   while servers can produce bytes with [send]. In particular, the
   [ObsToServer] effect observes a particular byte being sent to the
   server (by a test trace generator, intuitively). *)

Inductive observerE : Type -> Type :=
  | (* Observe the creation of a new connection *)
    ObsConnect : observerE connection_id
  | (* Observe a byte going into the server on a particular
       connection *)
    ObsToServer : connection_id -> observerE byte
    (* Observe a byte going out of the server. *)
  | ObsFromServer : connection_id -> observerE (option byte).

(* The [ObsFromServer] effect returns an [option], where [None] is a
   "hole" in the observed trace: it represents a message
   hypothetically sent by the server and that we haven't yet
   received. These holes allow us to keep exploring an observer even
   in the presence of partial outputs from the server. *)

(* The main event type for writing specifications: *)

Definition specE := failureE +' nondetE +' observerE.

(* ITree wrappers for the constructors: *)
Definition obs_connect :
  itree specE connection_id := embed ObsConnect.
Definition obs_to_server :
  connection_id -> itree specE byte := embed ObsToServer.
Definition obs_from_server :
  connection_id -> itree specE (option byte) := embed ObsFromServer.

(* Also some derived operations. *)

(* Make an assertion on a value, if it exists.  (If the value is
   [Some x] and the test returns false on [x], the [assert_on]
   ITree fails. *)
Parameter assert_on :
  forall {A}, string -> option A -> (A -> bool) -> itree specE unit.

(* Observe a message of fixed length sent to the server. *)
Parameter obs_msg_to_server : nat -> connection_id -> itree specE bytes.

(* Observe a message of fixed length received from the server and
   match it with an expected value, failing if they are not
   equal.  (This is implemented in terms of [obs_from_server] and
   [assert_on].  In particular, when [obs_from_server] returns [None],
   we want to assume that the hole stands for the next expected byte
   and continue past it.) *)
Parameter obs_msg_from_server : connection_id -> bytes -> itree specE unit.

End ObserverIface.
(* Implemented in [Lib.LinearSpec_Observer]. *)

(** ** Event traces *)

Module Type TracesIface (Server : ServerIface) (Observer : ObserverIface).
Import Server Observer.

(* The refinement relation between ITrees is stated in terms of _event
   traces_, which are simply lists of events.

   Events are parameterized by the type to represent the server's
   output. For specification purposes, an output is a plain
   [byte] ([real_event]). But for testing it will be useful to insert
   holes by instantiating [byte' := option byte]. *)

Inductive event (byte' : Type) :=
| NewConnection : connection_id -> event byte'
| ToServer : connection_id -> byte -> event byte'
| FromServer : connection_id -> byte' -> event byte'.

(* Traces are sequences of events. *)
Definition trace byte' := list (event byte').

(* In the real world, events carry concrete bytes. *)
Definition real_event := event byte.
Definition real_trace := list real_event.

(* For testing, it is useful to insert "hypothetical bytes" of unknown
   values in a trace, representing values that the server may have
   output but which have not reached the client yet. *)
Definition hypo_event := event (option byte).
Definition hypo_trace := list hypo_event.

(* Traces with holes are a superset of real traces. *)
Parameter real_to_hypo_trace : real_trace -> hypo_trace.
Coercion real_to_hypo_trace : real_trace >-> hypo_trace.

(* [is_impl_trace server tr] holds if [tr] is a trace of the [server].  *)
Parameter is_impl_trace : itree implE unit -> real_trace -> Prop.

(* [is_spec_trace observer tr] holds if [tr] is a trace of
   the [observer]; [tr] may contain holes. *)
Parameter is_spec_trace : itree specE unit -> hypo_trace -> Prop.

(* [Lib.Util.result] (from which [Lib.Util.simple_result] and
   [reordered_result] are derived) is a type with three
   constructors representing success, failure, or "don't know",
   possibly with a (counter)example. *)

(* QuickChick test for [is_spec_trace]. *)
Parameter is_spec_trace_test :
  itree specE unit -> hypo_trace -> simple_result.

End TracesIface.
(* This is implemented in [Lib.LinearSpec_Traces]. *)

(** Pause here and look at examples! *)

(* *)

(** ** Network Model *)

(* The above interfaces describe servers and observers that interact
   over a network, which we model as the following state machine... *)
Module Type NetworkModelIface.

(* The network state is a map from [connection_id] to connection
   states. *)

Section ConnectionState.

(* First, we define the type of a single connection
   state ([connection_state]).  Essentially, a connection can be seen
   as a pair of buffers that servers and clients push bytes to
   asynchronously.
      - Connections start in the [CLOSED] state.
      - When a client initiates a connection, the connection enters
        the [PENDING] state, and the client can immediately start
        sending messages over it.
      - The server must then accept the connection, which enters the
        [ACCEPTED] state, before receiving and sending messages over
        it. The client can now also receive messages. *)

Inductive connection_state_enum := CLOSED | PENDING | ACCEPTED.

Record connection_state :=
  Build_connection_state {

    (* The state of the connection (see above). *)
    connection_status : connection_state_enum;

    (* The buffer of bytes going into the server. *)
    connection_inbytes : list byte;

    (* The buffer of bytes going out from the server. *)
    connection_outbytes : list byte;
  }.

Definition initial_cs : connection_state := {|
    connection_status := CLOSED;
    connection_inbytes := [];
    connection_outbytes := [];
  |}.

End ConnectionState.

(* We can now define the complete state of the network
   as a map from [connection_id] to [connection_state]. *)
Definition network_state := Map.t connection_id connection_state.

(* Initial state: all connections are closed. *)
Definition initial_ns : network_state := fun _ => initial_cs.

(* State transitions.
   - The result is [None] when a transition is not defined.
   - Transitions may carry some output (in this case, a byte
     for [recv] transitions. *)
Definition transition (output : Type) : Type :=
  network_state -> option (network_state * output).

(* Each of the following possible transitions succeeds (returning a
   result and a next state) if the given transition is possible from
   the current network state. *)

(* Server-side transitions *)
Parameter server_accept : connection_id -> transition unit.
Parameter server_send : connection_id -> byte -> transition unit.
Parameter server_recv : connection_id -> transition byte.

(* Client-side transitions *)
Parameter client_connect : connection_id -> transition unit.
Parameter client_send : connection_id -> byte -> transition unit.
Parameter client_recv : connection_id -> transition byte.

End NetworkModelIface.
(* Implemented in [Lib.LinearSpec_NetworkModel]. *)

Module Type ReorderingIface
       (Server : ServerIface)
       (Observer : ObserverIface)
       (Traces : TracesIface Server Observer)
       (NetworkModel : NetworkModelIface).
Import Server Observer Traces NetworkModel.

(* These events label transitions in the network state machine
   defined above in [NetworkModelIface]. *)

(* Server-side interpretation of an event. *)
Definition server_transition (ev : real_event)
                           : network_state -> network_state -> Prop :=
  fun ns ns' =>
    match ev with
    | NewConnection _ c => server_accept c ns = Some (ns', tt)
    | ToServer _ c b => server_recv c ns = Some (ns', b)
    | FromServer _ c b => server_send c b ns = Some (ns', tt)
    end.

(* Client-side interpretation of an event. *)
Definition client_transition (ev : real_event) :
  network_state -> network_state -> Prop :=
  fun ns ns' =>
    match ev with
    | NewConnection _ c => client_connect c ns = Some (ns', tt)
    | ToServer _ c b => client_send c b ns = Some (ns', tt)
    | FromServer _ c b => client_recv c ns = Some (ns', b)
    end.

(* The main "reordering" relation. *)
(* [network_reordered_ ns tr str] holds when, starting from
   the network state [ns], there is an execution of the
   network with server-side trace [tr_server] and client-side
   trace [tr_client].

   We say that [tr_client] is a disordering of [tr_server],
   or that [tr_server] is a reordering of [tr_client]. *)
Inductive network_reordered_
                : network_state -> real_trace -> real_trace -> Prop :=
| ScrambleEmpty : forall ns, network_reordered_ ns [] []
| ScrambleServer : forall ns ns' e tr_server tr_client,
    server_transition e ns ns' ->
    network_reordered_ ns'       tr_server  tr_client ->
    network_reordered_ ns  (e :: tr_server) tr_client
| ScrambleClient : forall ns ns' e tr_server tr_client,
    client_transition e ns ns' ->
    network_reordered_ ns' tr_server       tr_client ->
    network_reordered_ ns  tr_server (e :: tr_client).

(* At the top level, we consider traces starting from the initial state. *)
Definition network_reordered := network_reordered_ initial_ns.

(* The main property defining our notion of "correctness". *)

(* The observable behavior of a server [impl] (resp. [spec])
   is the set of traces [tr] that are client-side reorderings
   of traces [tr_impl] of [impl] (resp. [tr_spec] of [spec]). *)
(* Defined in [Lib.LinearSpec_Server] *)
Definition impl_behavior (impl : itree implE unit)
  : real_trace -> Prop :=
  fun tr => exists tr_impl : real_trace,
      is_impl_trace impl tr_impl /\
      network_reordered tr_impl tr.

(* Defined in [Lib.LinearSpec_Observer] *)
Definition spec_behavior (spec : itree specE unit)
  : real_trace -> Prop :=
  fun tr => exists tr_spec : real_trace,
      is_spec_trace spec tr_spec /\
      network_reordered tr_spec tr.

(* A server ([impl : itree implE unit]) refines a "linear spec"
   ([spec : itree specE unit]) if, for every trace [tr_impl] that
   the server can produce, and every trace [tr] that can be observed
   from it via the network (i.e., a client-side reordering of
   [tr_impl]), it can be explained by a server-sider reordering
   of the "linear spec" [spec].
   Some examples can be found in [Spec.Descrambling_Examples].
 *)
Definition network_refines impl spec : Prop :=
  forall tr,
    impl_behavior impl tr -> spec_behavior spec tr.

(* Tests *)

(* Test result of reordering: success is witnessed by a
   reordered [hypo_trace]. *)
Definition reordered_result := result hypo_trace unit.

(* A test for [is_disordered_trace], which tries to
   reorder the given trace to a trace of the observer. *)
Parameter is_disordered_trace_test :
  itree specE unit -> real_trace -> reordered_result.

(* QuickChick test for [network_refines].  Checks that every trace
   of the server can be reordered into a trace of the observer. *)
Parameter network_refines_test :
  itree specE unit -> itree implE unit -> Checker.

End ReorderingIface.
(* The implementation of this interface is split in a couple of modules.
   The most important parts:
   - the definition of reordering is in [Lib.LinearSpec_Traces];
   - the general property [network_refines] is defined in
     [Lib.LinearSpec_Refinement];
   - the reordering function for a single trace,
     [is_disordered_trace_test] is in [Lib.LinearSpec_Scramble];
   - the test function for refinement, [network_refines_test]
     is in [Lib.LinearSpec_ServerTrace]. *)

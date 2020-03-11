(* Traces and reorderings. *)

(* We define the notion of trace and a "reordering"
   relation between the traces produced by a server and
   those that can be observed by a client on the other side
   of the network.

   The network is defined as a state machine with transitions
   visible either by the server or by the client;
   see [Lib.LinearSpec_NetworkModel].
 *)

Require Import Relations.
Require Import RelationClasses.

From QuickChick Require Import QuickChick.
From Custom Require Import List Show String.
Import ListNotations.
From Custom Require Map.

From DeepWeb.Free.Monad Require Import
     Free Common Traces.
Import SumNotations.

Require Import DeepWeb.Lib.Util.
Require Import DeepWeb.Lib.LinearSpec_NetworkModel.

Set Bullet Behavior "Strict Subproofs".

(* An event can be observed to happen on the network,
   either from the server's or the client's point of view.
   It is paremeterized by the type to represent the server's
   output... *)
Inductive event (byte' : Type) :=
| NewConnection : connection_id -> event byte'
| ToServer : connection_id -> byte -> event byte'
| FromServer : connection_id -> byte' -> event byte'
.

(* ... In the real world, this output is a concrete byte.
   (the other event type is [hypo_event], down below). *)
Definition real_event := event byte.

Arguments NewConnection {byte'}.
Arguments ToServer {byte'}.
Arguments FromServer {byte'}.

(* A trace is a sequence of events. *)
Definition trace byte' := list (event byte').
Definition real_trace := list real_event.

Definition server_transition (ev : real_event) 
                           : network_state -> network_state -> Prop :=
  fun ns ns' =>
    match ev with
    | NewConnection c => server_accept c ns = Some (ns', tt)
    | ToServer c b => server_recv c ns = Some (ns', b)
    | FromServer c b => server_send c b ns = Some (ns', tt)
    end.

Definition client_transition (ev : real_event) :
  network_state -> network_state -> Prop :=
  fun ns ns' =>
    match ev with
    | NewConnection c => client_connect c ns = Some (ns', tt)
    | ToServer c b => client_send c b ns = Some (ns', tt)
    | FromServer c b => client_recv c ns = Some (ns', b)
    end.

(* The main "reordering" relation. *)
(* Corresponding "server-side" and "client-side" traces. *)
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
    network_reordered_ ns  tr_server (e :: tr_client)
.

Definition network_reordered := network_reordered_ initial_ns.

Definition event_connection {byte'} (ev : event byte') :
  connection_id :=
  match ev with
  | NewConnection c' => c'
  | ToServer c' _ => c'
  | FromServer c' _ => c'
  end.

(* Some notations to make traces readable. *)
Module EventNotations.
Delimit Scope event_scope with event.

(* Connection [c] is open. *)
Notation "c !" := (NewConnection (Connection c))
(at level 30) : real_scope.

(* Byte [b] goes to the server on connection [c]. *)
Notation "c <-- b" := (ToServer (Connection c) b%char)
(at level 30) : real_scope.

(* Byte [b] goes out of the server on connection [c]. *)
Notation "c --> b" := (FromServer (Connection c) b%char)
(at level 30) : real_scope.

Notation "c !" := (NewConnection (Connection c) : event (option byte))
(at level 30) : hypo_scope.

(* Byte [b] goes to the server on connection [c]. *)
Notation "c <-- b" :=
  (ToServer (Connection c) b%char : event (option byte))
(at level 30) : hypo_scope.

(* Byte [b] goes out of the server on connection [c]. *)
Notation "c --> b" :=
  (FromServer (Connection c) (Some b)%char : event (option byte))
(at level 30) : hypo_scope.

(* Unknown byte goes out of the server on connection [c]. *)
Notation "c --> ?" := (FromServer (Connection c) None : event (option byte))
(at level 30) : hypo_scope.

(* Open Scope real_scope. *)

Delimit Scope hypo_scope with hypo.
Delimit Scope real_scope with real.

End EventNotations.

(* With the [network_reordered] relation we defined here, we
   can state the correctness property we generally want to test
   and verify about server itrees, in
   [Lib.LinearSpec_Refinement]. It is specialized to the
   swap server in [Spec.TopLevelSpec]. *)




(*************** Internals ******************)

(* Basic predicates *)

Definition is_Connect {byte' : Type} (ev : event byte') :=
  match ev with
  | NewConnection _ => true
  | _ => false
  end.

Definition is_FromServer {byte' : Type} (ev : event byte') :=
  match ev with
  | FromServer _ _ => true
  | _ => false
  end.

Definition is_ToServer {byte' : Type} (ev : event byte') :=
  match ev with
  | ToServer _ _ => true
  | _ => false
  end.

(* Misc combinators. *)

Fixpoint fold_transition {event}
           (P : event -> relation network_state)
           (evs : list event) : relation network_state :=
  match evs with
  | [] => fun ns ns' => ns = ns'
  | ev :: evs => fun ns ns'' =>
    exists ns', P ev ns ns' /\ fold_transition P evs ns' ns''
  end.

Definition server_transitions :
  real_trace -> relation network_state :=
  fold_transition server_transition.

Definition client_transitions :
  real_trace -> relation network_state :=
  fold_transition client_transition.

Definition to_server_trace (c : connection_id) (s : bytes) :
  real_trace :=
  map (ToServer c) (list_of_bytes s).

Definition from_server_trace (c : connection_id) (s : bytes) :
  real_trace :=
  map (FromServer c) (list_of_bytes s).

(* Traces with holes. *)

(* It will also be useful for testing to insert hypothetical
   bytes of unknown values in a trace, representing values that the
   server may have output but which have not reached the client yet. *)
Definition hypo_event := event (option byte).
Definition hypo_trace := list hypo_event.

(* We can convert real things to hypothetical things. *)

Definition real_to_hypo_event : real_event -> hypo_event :=
  fun ev =>
    match ev with
    | NewConnection c => NewConnection c
    | ToServer c b => ToServer c b
    | FromServer c b => FromServer c (Some b)
    end.

Coercion real_to_hypo_event : real_event >-> hypo_event.

Definition real_to_hypo_trace : real_trace -> hypo_trace :=
  map real_to_hypo_event.

Coercion real_to_hypo_trace : real_trace >-> hypo_trace.

(* Events and effects *)

(* Show instances *)

Definition show_real_event (ev : real_event) :=
  match ev with
  | NewConnection c => (show c ++ " !")%string
  | ToServer c b =>
    (show c ++ " <-- " ++ show b)%string
  | FromServer c b =>
    (show c ++ " --> " ++ show b)%string
  end.

Instance Show_real_event: Show real_event :=
  { show := show_real_event }.

Definition show_hypo_event (ev : hypo_event) :=
  match ev with
  | NewConnection c => (show c ++ " !")%string
  | ToServer c b =>
    (show c ++ " <-- " ++ show b)%string
  | FromServer c ob =>
    (show c ++ " --> " ++ match ob with
                          | Some b => show b
                          | None => "?"
                          end)%string
  end.

Instance Show_hypo_event: Show hypo_event :=
  { show := show_hypo_event }.

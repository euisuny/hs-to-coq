(* A model of the network. *)

From Custom Require Import
     List.
Import ListNotations.

From Custom Require
     Map.

From DeepWeb Require Import
     Lib.Util.

Set Bullet Behavior "Strict Subproofs".

(* The network state is a map from [connection_id]
   to the state of the connection ([connection_state]). *)

(* We start by defining the state of a single connection. *)

(* - Connections start in the [CLOSED] state.
   - When a client initiates a connection ([client_connect]),
     the connection enters the [PENDING] state, and the client can
     immediately start sending messages over it.
   - The server must then accept the connection, which enters
     the [ACCEPTED] state, before receiving and sending messages
     over it. The client can now also receive messages.
 *)
Inductive connection_state_enum := CLOSED | PENDING | ACCEPTED.

(* A connection can be seen as a pair of buffers. *)
Record connection_state :=
  Build_connection_state {

    (* The state of the connection (see above). *)
    connection_status : connection_state_enum;

    (* The buffer of bytes going into the server. *)
    connection_inbytes : list byte;

    (* The buffer of bytes going out from the server. *)
    connection_outbytes : list byte;
  }.

(* Connections start [CLOSED]. *)
(* "cs" for [connection_state]. *)
Definition initial_cs : connection_state := {|
    connection_status := CLOSED;
    connection_inbytes := [];
    connection_outbytes := [];
  |}.

(* A client-side "connect" updates the connection from [CLOSED]
   to [PENDING]. *)
Definition pending_cs : connection_state := {|
    connection_status := PENDING;
    connection_inbytes := [];
    connection_outbytes := [];
  |}.

(* A server-side "accept" updates the connection from [PENDING]
   to [ACCEPTED]. There may already be bytes going into the
   server that we must preserve. *)
Definition accept_cs (cs : connection_state) : connection_state := {|
    connection_status := ACCEPTED;
    connection_inbytes := connection_inbytes cs;
    connection_outbytes := [];
  |}.

(* A client sends a byte to the server on some connection by
   adding it to the connection's "in"-buffer. *)
Definition update_in (bs : list byte) (cs : connection_state) :
  connection_state := {|
    connection_status := connection_status cs;
    connection_inbytes := bs;
    connection_outbytes := connection_outbytes cs;
  |}.

(* A server sends a byte to the client by adding it to the
   connection's "out"-buffer. *)
Definition update_out (bs : list byte) (cs : connection_state) :
  connection_state := {|
    connection_status := connection_status cs;
    connection_inbytes := connection_inbytes cs;
    connection_outbytes := bs;
  |}.

(* We can now define the complete state of the network. *)
Definition network_state := Map.t connection_id connection_state.

(* Initial state. *)
(* "ns" for [network_state]. *)
Definition initial_ns : network_state := fun _ => initial_cs.

(* State transitions (see [NetworkModelInterface]). *)
Definition transition (output : Type) : Type :=
  network_state -> option (network_state * output).

(* The client opens a new connection.
   The result is [Some] if and only if the connection is [CLOSED],
   and it then moves to the [PENDING] state, waiting to be accepted
   by the server. *)
Definition client_connect (c : connection_id) : transition unit :=
  fun (ns : network_state) =>
    let cs := Map.lookup ns c in
    match connection_status cs with
    | CLOSED => Some (Map.update c pending_cs ns, tt)
    | PENDING | ACCEPTED => None
    end.

Lemma connect_success ns c :
  connection_status (Map.lookup ns c) = CLOSED ->
  client_connect c ns = Some (Map.update c pending_cs ns, tt).
Proof.
  intro Hc.
  unfold client_connect.
  rewrite Hc; auto.
Qed.

Lemma client_connect_success ns ns' c :
  client_connect c ns = Some (ns', tt)
  <->
  connection_status (Map.lookup ns c) = CLOSED /\
  ns' = Map.update c pending_cs ns.
Proof.
  unfold client_connect.
  split.
  - destruct connection_status; try discriminate; auto.
    intro H; inversion H; auto.
  - intros [H1 H2]; rewrite H1; subst ns'; auto.
Qed.

(* The server accepts a [PENDING] connection.
   The result is [Some] if and only if the connection is [PENDING],
   and it then moves to the [ACCEPTED] state, indicating that the
   server can send and recv messages on it. *)
Definition server_accept (c : connection_id) : transition unit :=
  fun ns =>
    let cs := Map.lookup ns c in
    match connection_status cs with
    | PENDING => Some (Map.update c (accept_cs cs) ns, tt)
    | ACCEPTED | CLOSED => None
    end.

Lemma accept_success ns c :
  let cs := Map.lookup ns c in
  connection_status cs = PENDING ->
  server_accept c ns = Some (Map.modify c accept_cs ns, tt).
Proof.
  unfold server_accept.
  simpl; intro Hc.
  rewrite Hc; auto.
Qed.

Lemma server_accept_success ns ns' c :
  server_accept c ns = Some (ns', tt)
  <->
  connection_status (Map.lookup ns c) = PENDING /\
  ns' = Map.modify c accept_cs ns.
Proof.
  unfold server_accept.
  split.
  - destruct connection_status; try discriminate; auto.
    intro H; inversion H; auto.
  - intros [H1 H2]; rewrite H1; subst ns'; auto.
Qed.

(* The server receives a byte [b] on connection [c].
   The connection [c] must be [ACCEPTED], and the
   [connection_inbytes] buffer must be nonempty. *)
Definition server_recv (c : connection_id) : transition byte :=
  fun ns =>
    let cs := Map.lookup ns c in
    match connection_status cs with
    | ACCEPTED =>
      match connection_inbytes cs with
      | [] => None
      | b :: bs =>
        let cs := update_in bs cs in
        let ns := Map.update c cs ns in
        Some (ns, b)
      end
    | PENDING | CLOSED => None
    end.

Lemma server_recv_success ns ns' c b :
  let bs := connection_inbytes (Map.lookup ns' c) in
  server_recv c ns = Some (ns', b)
  <->
  ns' = Map.modify c (update_in bs) ns /\
  let cs := Map.lookup ns c in
  (connection_status cs = ACCEPTED /\
   connection_inbytes cs = b :: bs).
Proof.
  unfold server_recv.
  split.
  - destruct connection_status, connection_inbytes;
      try discriminate.
    intros H; inversion H; subst.
    rewrite Map.update_lookup_eq by reflexivity.
    repeat split; auto.
  - simpl; intros [Hns [Hc Hb]].
    rewrite Hc, Hb.
    f_equal. f_equal. auto.
Qed.

(* The server sends a byte [b] on connection [c].
   The connection [c] must be [ACCEPTED]. *)
Definition server_send
           (c : connection_id) (b : byte) : transition unit :=
  fun ns =>
    let cs := Map.lookup ns c in
    match connection_status cs with
    | ACCEPTED =>
      let cs := update_out (connection_outbytes cs ++ [b]) cs in
      Some (Map.update c cs ns, tt)
    | PENDING | CLOSED => None
    end.

Lemma server_send_success ns ns' c b :
  server_send c b ns = Some (ns', tt) <->
  let cs := Map.lookup ns c in
  ns' = Map.modify
          c (fun cs => update_out (connection_outbytes cs ++ [b]) cs)
          ns /\
  connection_status cs = ACCEPTED.
Proof.
  unfold server_send.
  split.
  - destruct connection_status;
      try discriminate.
    intro H; inversion H; auto.
  - intros [Hns Hc].
    rewrite Hc. rewrite Hns; auto.
Qed.

(* The client receives a byte sent by the server on connection [c].
   The connection [c] must be [ACCEPTED] (the server must
   accept a connection before sending bytes on it),
   and the [connections_outbytes] buffer must be nonempty. *)
Definition client_recv (c : connection_id) : transition byte :=
  fun ns =>
    let cs := Map.lookup ns c in
    match connection_status cs with
    | ACCEPTED =>
      match connection_outbytes cs with
      | [] => None
      | b :: bs =>
        let cs := update_out bs cs in
        let ns := Map.update c cs ns in
        Some (ns, b)
      end
    | PENDING | CLOSED => None
    end.

Lemma client_recv_success ns ns' c b :
  let bs := connection_outbytes (Map.lookup ns' c) in
  client_recv c ns = Some (ns', b)
  <->
  ns' = Map.modify c (update_out bs) ns /\
  let cs := Map.lookup ns c in
  (connection_status cs = ACCEPTED /\
   connection_outbytes cs = b :: bs).
Proof.
  unfold client_recv.
  split.
  - destruct connection_status, connection_outbytes;
      try discriminate.
    intros H; inversion H; subst.
    rewrite Map.update_lookup_eq by reflexivity.
    repeat split; auto.
  - simpl; intros [Hns [Hc Hb]].
    rewrite Hc, Hb.
    f_equal. f_equal. auto.
Qed.

(* The client sends a byte [b] to the server on connection [c].
   The connection [c] must be [PENDING] or [ACCEPTED]. *)
Definition client_send
           (c : connection_id) (b : byte) : transition unit :=
  fun ns =>
    let cs := Map.lookup ns c in
    match connection_status cs with
    | ACCEPTED | PENDING =>
      let cs := update_in (connection_inbytes cs ++ [b]) cs in
      Some (Map.update c cs ns, tt)
    | CLOSED => None
    end.

Lemma client_send_success ns ns' c b :
  client_send c b ns = Some (ns', tt) <->
  let cs := Map.lookup ns c in
  ns' = Map.modify
          c (fun cs => update_in (connection_inbytes cs ++ [b]) cs)
          ns /\
  ( connection_status cs = PENDING \/
    connection_status cs = ACCEPTED
  ).
Proof.
  unfold client_send.
  split.
  - destruct connection_status;
      try discriminate.
    + intro H; inversion H; split; auto.
    + intro H; inversion H; split; auto.
  - intros [Hns [Hc | Hc]];
      rewrite Hc; rewrite Hns; auto.
Qed.

Lemma update_in_idem : forall st,
    update_in (connection_inbytes st) st = st.
Proof. intros []; auto. Qed.

Lemma update_update_in : forall st x y,
    update_in y (update_in x st) = update_in y st.
Proof. intros []; auto. Qed.

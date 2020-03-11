(*! Section BaseTest *)

(* * The implementation model *)

(* - The toplevel itree representing the C program [main.c] is [server].
   - The main loop body is [select_loop_body].
   - The logic of processing connections mainly lives in
     [conn_read] and [conn_send]. *)

(* This file uses effects from [Lib.NetworkInterface]. *)

Generalizable Variable E.

From DeepWeb.Free.Monad
     Require Import Free Common.

From QuickChick Require Import Decidability.

From Custom Require Import List.
Import ListNotations.

From DeepWeb Require Import
     Lib.NetworkInterface
     Lib.NetworkAdapter
     Lib.LinearSpec
     Lib.Socket
     Spec.ServerDefs.

From Coq Require Import String Arith.
Local Open Scope string_scope.

Import SocketAPI.

From Custom Require Monad.
Import MonadNotations.

(** * Low-level "C-Like" Specification of the Swap Server *)
Section Impl.

Variable (app : App.t).

Inductive connection_state : Type :=
  RECVING | SENDING | DONE | DELETED.

Record connection : Type :=
  { 
    conn_id : connection_id;
    conn_request : string;
    conn_response : string;
    conn_response_bytes_sent : nat;
    conn_state : connection_state
  }.

Definition upd_conn_request (conn : connection) (request : string)
                          : connection :=
  {|
    conn_id := conn_id conn;
    conn_request := request;
    conn_response := conn_response conn;
    conn_response_bytes_sent := conn_response_bytes_sent conn;
    conn_state := conn_state conn
  |}.


Definition upd_conn_response (conn : connection) (response : string)
                           : connection :=
  {|
    conn_id := conn_id conn;
    conn_request := conn_request conn;
    conn_response := response;
    conn_response_bytes_sent := conn_response_bytes_sent conn;
    conn_state := conn_state conn
  |}.

Definition upd_conn_response_bytes_sent
           (conn : connection) (response_bytes_sent : nat)
         : connection :=
  {|
    conn_id := conn_id conn;
    conn_request := conn_request conn;
    conn_response := conn_response conn;
    conn_response_bytes_sent := response_bytes_sent;
    conn_state := conn_state conn
  |}.

Definition upd_conn_state (conn : connection) (state : connection_state)
                        : connection :=
  {|
    conn_id := conn_id conn;
    conn_request := conn_request conn;
    conn_response := conn_response conn;
    conn_response_bytes_sent := conn_response_bytes_sent conn;
    conn_state := state
  |}.

Definition accept_connection (addr : endpoint_id):
  itree socketE (option connection) :=
  or (client_conn <- accept addr ;;
      or (* possible internal malloc failure *)
        (ret (Some {| conn_id := client_conn ;
                      conn_request := "";
                      conn_response := "";
                      conn_response_bytes_sent := 0;
                      conn_state := RECVING |}))
        (r <- shutdown client_conn ;;
         ret None))
     (ret None).

Global Instance dec_eq_connection_state {st1 st2 : connection_state}
                               : Dec (st1 = st2).
Proof. dec_eq. Defined.

Hint Resolve dec_eq_connection_state.

Global Instance dec_connection {c1 c2 : connection} : Dec (c1 = c2).
Proof. dec_eq. Defined.

Global Instance dec_eq_connection : Dec_Eq connection.
Proof. constructor. intros x y. apply dec_connection. Defined.

Class HasConnectionState (A : Type) :=
  { get_conn_state : A -> connection_state }.

Global Instance connection_has_connection_state : HasConnectionState connection.
Proof. constructor. intros. apply conn_state. assumption. Defined.

Definition has_conn_state {A} `{HasConnectionState A}
           (st : connection_state) (conn : A) : bool :=
  ssrbool.is_left
    (@dec (st = get_conn_state conn) _).

(* Wait for a message from connection [conn].
   [recv] can return a partial message, in which case we store the
   bytes we received to try receiving more in a late. iteration. *)
Definition conn_read
           (conn: connection) (s : App.state app)
  : itree socketE (connection * App.state app) :=
  let req_len := String.length (conn_request conn) in
  or (r <- recv (conn_id conn) (App.req_size app - req_len) ;;
      match r with
        (* If [recv] returns [r = None], the connection was closed. *)
      | None => ret (upd_conn_state conn DELETED, s)
        (* Otherwise, we append the received bytes to the other
           bytes previously received on that connection. *)
      | Some msg =>
        let msg_len := String.length msg in
        let msg' := (*!*) (conn_request conn ++ msg)%string
                    (*!! Respond too quickly *)
                    (*! "BAD" *) in
        if is_complete app msg' then
          (* If the client's message is complete (i.e., of
             length [buffer_size]) we prepare to respond with
             [last_full_msg] and store the [msg'] for the next
             exchange. *)
          let '(s', resp) := App.app app (s, msg') in
          let conn' :=  {| conn_id := conn_id conn ;
                           conn_request := msg';
                           conn_response := resp;
                           conn_response_bytes_sent := 0;
                           conn_state := SENDING
                        |}
          in ret (conn', s')
        else
          (* Otherwise we wait for more input from this connection. *)
          let conn' := {| conn_id := conn_id conn ;
                          conn_request := msg';
                          conn_response := conn_response conn;
                          conn_response_bytes_sent := conn_response_bytes_sent conn;
                          conn_state := RECVING
                       |}
          in ret (conn', s)
      end
     )
     (ret (conn, s)).

(* Send a response on connection [conn].
   [send_any_prefix] (representing the [send] POSIX syscall)
   may send only a prefix of the message (it returns the length [r]
   of that prefix), in which case we will retry sending the rest
   in a later iteration. *)
Definition conn_write (conn: connection) : itree socketE connection :=
  or (let num_bytes_sent := conn_response_bytes_sent conn in
      r <- send_any_prefix
            (conn_id conn)
            (substring num_bytes_sent
                       (String.length (conn_response conn) - num_bytes_sent)
                       (conn_response conn)) ;;
      if (String.length (conn_response conn) <? r)%nat
      then
        (* The sent prefix [r] must be no longer than the actual
           message to send. *)
        fail "dead code"
      else
        let num_bytes_sent := conn_response_bytes_sent conn + r in
        if Nat.eqb num_bytes_sent (String.length (conn_response conn)) then
          (* The whole message got sent, we start waiting for another
             message on this connection. *)
          ret {| conn_id := conn_id conn;
                 conn_request := "";
                 conn_response := "";
                 conn_response_bytes_sent := 0;
                 conn_state := RECVING
              |}
        else
          (* Only part of the message was sent, retry. *)
          ret {| conn_id := conn_id conn;
                 conn_request := conn_request conn;
                 conn_response := conn_response conn;
                 conn_response_bytes_sent := num_bytes_sent;
                 conn_state := conn_state conn
              |}
     )
     (* Internal errors can happen, then we discard the connection. *)
     (ret (upd_conn_state conn DELETED)).

(* Call [conn_read] or [conn_write] depending on the state
   of the connection. *)
Definition process_conn (conn: connection) (s : App.state app)
          : itree socketE (connection * App.state app) :=
  match conn_state conn with
  | RECVING => conn_read conn s
  | SENDING =>
    conn' <- conn_write conn ;;
    ret (conn', s)
  | _ => ret (conn, s)
  end.

Definition replace_active conn' connections :=
  replace_when
    (fun c =>
       if (has_conn_state RECVING c
           || has_conn_state SENDING c)%bool
       then (conn_id c = conn_id conn' ?)
       else false)
    conn'
    connections.

Arguments replace_active _ _ /.

(* Choose one connection to run [process_conn] with. *)
(* The returned [bool] is always true and is just waiting to
   be removed in the next refactoring. *)
(* 
   In the paper, [select_loop_body ...] is of type [itree implE ...] 
   instead of [itree socketE ...]. This is for simplicity. 
   We have a function [simplify_network] that transforms a tree over [socketE]
   to one that is over [implE].
 *)

Definition select_loop_body
  (server_addr : endpoint_id)
  (server_st : list connection * App.state app)
  : itree socketE (list connection * App.state app)
  :=
  let '(conns, s) := server_st in
  or
    (r <- accept_connection server_addr ;;
     match r with
     | Some c => ret (c::conns, s)
     | None   => ret (conns, s)
     end)
    (let waiting_to_recv := 
         filter (has_conn_state RECVING) conns in
     let waiting_to_send := 
         filter (has_conn_state SENDING) conns in
     c <- choose (waiting_to_recv++waiting_to_send);;
     new_st <- process_conn c s;;
     let '(c', s') := new_st in
     let conns' :=
         replace_when
           (fun x =>
              if (has_conn_state RECVING x
               || has_conn_state SENDING x)%bool
              then (conn_id x = conn_id c' ?)
              else false)
           c'
           conns in
     ret (conns', s')
    ).

Definition select_loop
                (server_addr : endpoint_id)
              : (list connection * App.state app)
                  -> itree socketE Empty_set :=
  loop_with_state (fun server_st =>
    select_loop_body server_addr server_st).

Definition server_ (endpoint : endpoint_id) :=
  (or (listen endpoint ;;
       select_loop endpoint ([], App.initial_state app) ;;
       ret tt)
      (* The server can just fail to start during initialization. *)
      (ret tt)).

Definition server := server_ SERVER_PORT.

Import LinearSpec_Server.

(* Adapted to [implE] interface. *)
Definition server' : itree implE unit := simplify_network server.

End Impl.

Definition real_swap_impl := server real_swap_app.
Definition real_swap_impl' := server' real_swap_app.
Definition test_swap_impl' := server' test_swap_app.

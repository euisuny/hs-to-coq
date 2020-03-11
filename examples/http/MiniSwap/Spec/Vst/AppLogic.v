Require Import String.

From DeepWeb.Lib Require Import
     VstLib.

From DeepWeb.Spec Require Import
     Vst.MainInit
     Vst.SocketSpecs
     ServerDefs
     Swap_ImplModel.

Require Import DeepWeb.Lib.VstLib.

Import SockAPIPred.
Import TracePred.

Open Scope logic.
Open Scope list.
Local Close Scope Z.

Set Bullet Behavior "Strict Subproofs".

(***************************** Application Logic ******************************)

Section AppLogic.
Variable (app : App.t).

Inductive recv_step :
  (connection * sockfd * SocketMap * App.state app) ->
  (connection * sockfd * SocketMap * App.state app) -> Prop :=
| Conn_RECVING_RECVING:
    forall (conn : connection) (fd : sockfd) (sock_st : SocketMap)
      (app_s : App.state app)
      (recved_msg : string)
      (conn' : connection),
      (* TODO: Factor out this assumption. *)
      App.req_size app <= Z.to_nat SIZE_MAX ->
      conn_state conn = RECVING ->
      conn' = {| conn_id := conn_id conn;
                 conn_request := (conn_request conn) ++ recved_msg;
                 conn_response := conn_response conn;
                 conn_response_bytes_sent := conn_response_bytes_sent conn;
                 conn_state := RECVING
              |} ->
      lookup_socket sock_st fd = ConnectedSocket (conn_id conn) ->
      length (val_of_string (conn_request conn')) <= App.req_size app ->
      recv_step (conn, fd, sock_st, app_s)
                (conn', fd, sock_st, app_s)
| Conn_RECVING_SENDING:
    forall (conn : connection) (fd : sockfd) (sock_st : SocketMap)
      (app_s app_s' : App.state app)
      (recved_msg resp : string)
      (conn' : connection),
      let full_request := (conn_request conn ++ recved_msg)%string in
      App.req_size app <= Z.to_nat SIZE_MAX ->
      length (val_of_string (conn_request conn')) <= App.req_size app ->
      conn_state conn = RECVING ->
      is_complete app full_request = true ->
      (app_s', resp) = App.app app (app_s, full_request) ->
      conn' = {| conn_id := conn_id conn;
                 conn_request := full_request;
                 conn_response := resp;
                 conn_response_bytes_sent := 0;
                 conn_state := SENDING
              |} ->
      lookup_socket sock_st fd = ConnectedSocket (conn_id conn) ->
      recv_step (conn, fd, sock_st, app_s)
                (conn', fd, sock_st, app_s')
| Conn_RECVING_EOF:
    forall (conn : connection) (fd : sockfd) (sock_st : SocketMap)
      (app_s : App.state app)
      (conn' : connection) (sock_st' : SocketMap),
      App.req_size app <= Z.to_nat SIZE_MAX ->
      conn_state conn = RECVING ->
      conn' = {| conn_id := conn_id conn;
                 conn_request := conn_request conn;
                 conn_response := conn_response conn;
                 conn_response_bytes_sent := conn_response_bytes_sent conn;
                 conn_state := DELETED
              |} ->
      lookup_socket sock_st fd = ConnectedSocket (conn_id conn) ->
      sock_st' = update_socket_state sock_st fd OpenedSocket ->
      recv_step (conn, fd, sock_st, app_s)
                (conn', fd, sock_st', app_s)
| Conn_RECVING_Id:
    forall (conn : connection) (fd : sockfd) (sock_st : SocketMap)
      (app_s : App.state app),
      App.req_size app <= Z.to_nat SIZE_MAX ->
      recv_step (conn, fd, sock_st, app_s)
                (conn, fd, sock_st, app_s).

Inductive send_step:
  (connection * sockfd * SocketMap) ->
  (connection * sockfd * SocketMap) -> Prop :=
| Conn_SENDING_SENDING:
    forall (conn : connection) (fd : sockfd) (sock_st : SocketMap)
      (num_bytes_sent : nat) (conn' : connection),
      conn_state conn = SENDING ->
      num_bytes_sent >= 0 ->
      let response_length := length (val_of_string (conn_response conn)) in
      let total_num_bytes_sent :=
          conn_response_bytes_sent conn + num_bytes_sent in
      total_num_bytes_sent < response_length ->
      conn' = {| conn_id := conn_id conn;
                 conn_request := conn_request conn;
                 conn_response := conn_response conn;
                 conn_response_bytes_sent := total_num_bytes_sent;
                 conn_state := SENDING
              |} ->
      lookup_socket sock_st fd = ConnectedSocket (conn_id conn) ->
      send_step (conn, fd, sock_st) (conn', fd, sock_st)
| Conn_SENDING_RECVING:
    forall (conn : connection) (fd : sockfd) (sock_st : SocketMap)
      (num_bytes_sent : nat) (conn' : connection),
      conn_state conn = SENDING ->
      let response_length := length (val_of_string (conn_response conn)) in
      let total_num_bytes_sent :=
          conn_response_bytes_sent conn + num_bytes_sent in
      total_num_bytes_sent = response_length ->
      conn' = {| conn_id := conn_id conn;
                 conn_request := "";
                 conn_response := "";
                 conn_response_bytes_sent := 0;
                 conn_state := RECVING
              |} ->
      lookup_socket sock_st fd = ConnectedSocket (conn_id conn) ->
      send_step (conn, fd, sock_st) (conn', fd, sock_st)
| Conn_SENDING_Fail:
    forall (conn : connection) (fd : sockfd) (sock_st : SocketMap)
      (conn' : connection) (sock_st' : SocketMap),
      conn' = {| conn_id := conn_id conn;
                 conn_request := conn_request conn;
                 conn_response := conn_response conn;
                 conn_response_bytes_sent := conn_response_bytes_sent conn;
                 conn_state := DELETED
              |} ->
      (sock_st' = sock_st \/
       sock_st' = update_socket_state sock_st fd OpenedSocket) ->
      send_step (conn, fd, sock_st) (conn', fd, sock_st').


Inductive consistent_state
  : SocketMap -> (connection * sockfd) -> Prop :=
| Consistent_RECVING:
    forall (client_fd : sockfd) (client_id : connection_id) (request : string)
      (conn: connection) (sock_st : SocketMap),
      (* TODO Factor out these assumptions. *)
      App.req_size app <= Z.to_nat SIZE_MAX ->
      length (val_of_string (conn_request conn)) <= App.req_size app ->
      (descriptor (client_fd) < FD_SETSIZE)%Z ->
      conn = {| conn_id := client_id ;
                conn_request := request;
                conn_response := "";
                conn_response_bytes_sent := 0;
                conn_state := RECVING
             |} ->
      lookup_socket sock_st client_fd = ConnectedSocket client_id ->
      consistent_state sock_st (conn, client_fd)
| Consistent_SENDING:
    forall (client_fd : sockfd) (client_id : connection_id)
      (request : string) (response: string) (num_bytes_sent : nat)
      (conn: connection) (sock_st : SocketMap),
      App.req_size app <= Z.to_nat SIZE_MAX ->
      length (val_of_string (conn_request conn)) <= App.req_size app ->
      (descriptor (client_fd) < FD_SETSIZE)%Z ->
      conn = {| conn_id := client_id ;
                conn_request := request;
                conn_response := response;
                conn_response_bytes_sent := num_bytes_sent;
                conn_state := SENDING
             |} ->
      lookup_socket sock_st client_fd = ConnectedSocket client_id ->
      is_complete app request = true ->
      num_bytes_sent <= length (val_of_string response) ->
      consistent_state sock_st (conn, client_fd)
| Consistent_DELETED:
    forall (client_fd : sockfd) (client_id : connection_id)
      (request : string) (response : string)
      (num_bytes_sent : nat)
      (conn: connection) (sock_st : SocketMap),
      App.req_size app <= Z.to_nat SIZE_MAX ->
      length (val_of_string (conn_request conn)) <= App.req_size app ->
      (descriptor client_fd < FD_SETSIZE)%Z ->
      conn = {| conn_id := client_id;
                conn_request := request;
                conn_response := response;
                conn_response_bytes_sent := num_bytes_sent;
                conn_state := DELETED
             |} ->
      (lookup_socket sock_st client_fd = OpenedSocket \/
       lookup_socket sock_st client_fd = ConnectedSocket client_id) ->
      num_bytes_sent <= length (val_of_string response) ->
      consistent_state sock_st (conn, client_fd).

End AppLogic.

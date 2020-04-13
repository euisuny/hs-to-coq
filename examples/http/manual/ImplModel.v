Require Import ServerDefs.
From Coq Require Import String.
From ExtLib Require Import Monad.
Import MonadNotation.
Open Scope monad_scope.

Section Impl.

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

(* runConn :: (Socket, SockAddr) -> IO () *)
(* runConn (sock, _) = do *)
(*   -- Send data to socket. Socket must be connected to a remote socket. returns *)
(*   -- number of bytes sent. Apps are responsible for ensuring all data has been sent. *)
(*   send sock "Hello World!\n" *)
(*   -- `close` does not throw exceptions *)
(*   close sock *)

  (* Definition runConn *)
  (*   : (NetworkTypes.Socket * NetworkTypes.SockAddr)%type -> IO.IO unit := *)
  (*   fun '(pair sock _) => *)
  (*     Network_.send sock (GHC.Base.hs_string__ "Hello World!") GHC.Base.>> *)
  (*     Network_.close sock. *)

  (* Definition runConn (addr : endpoint_id): *)
  (*   itree socketE (option connection) := *)
  (*   or (client_conn <- send connection_id "Hello World!\n"). *)


Definition mainLoop : NetworkTypes.Socket -> IO.IO unit :=
  fun (sock : NetworkTypes.Socket) =>
    (@ITree.forever IO.ioE unit unit (Network_.accept sock GHC.Base.>>=
      (fun conn => runConn conn))).

Definition main : IO.IO unit :=
  Network_.socket NetworkTypes.AF_INET NetworkTypes.Stream #0 GHC.Base.>>=
  (fun sock =>
     Network_.setSocketOption sock NetworkTypes.ReuseAddr #1 GHC.Base.>>
     (Network_.bind sock (NetworkTypes.SockAddrInet #4242 NetworkTypes.iNADDR_ANY)
      GHC.Base.>>
      (Network_.listen sock #2 GHC.Base.>> mainLoop sock))).

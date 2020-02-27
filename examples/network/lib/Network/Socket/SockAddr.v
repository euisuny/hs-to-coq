(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Converted imports: *)

Require GHC.Num.
Require GHC.Ptr.
Require IO.
Require Network.Socket.Buffer.
Require Network.Socket.Name.
Require Network.Socket.Syscall.
Require NetworkTypes.

(* No type declarations to convert. *)

(* Converted value declarations: *)

Definition sendBufTo {a}
   : NetworkTypes.Socket ->
     GHC.Ptr.Ptr a -> GHC.Num.Int -> NetworkTypes.SockAddr -> IO.IO GHC.Num.Int :=
  Network.Socket.Buffer.sendBufTo.

Definition recvBufFrom {a}
   : NetworkTypes.Socket ->
     GHC.Ptr.Ptr a ->
     GHC.Num.Int -> IO.IO (GHC.Num.Int * NetworkTypes.SockAddr)%type :=
  Network.Socket.Buffer.recvBufFrom.

Definition getSocketName : NetworkTypes.Socket -> IO.IO NetworkTypes.SockAddr :=
  Network.Socket.Name.getSocketName.

Definition getPeerName : NetworkTypes.Socket -> IO.IO NetworkTypes.SockAddr :=
  Network.Socket.Name.getPeerName.

Definition connect
   : NetworkTypes.Socket -> NetworkTypes.SockAddr -> IO.IO unit :=
  Network.Socket.Syscall.connect.

Definition bind : NetworkTypes.Socket -> NetworkTypes.SockAddr -> IO.IO unit :=
  Network.Socket.Syscall.bind.

Definition accept
   : NetworkTypes.Socket ->
     IO.IO (NetworkTypes.Socket * NetworkTypes.SockAddr)%type :=
  Network.Socket.Syscall.accept.

(* External variables:
     op_zt__ unit GHC.Num.Int GHC.Ptr.Ptr IO.IO Network.Socket.Buffer.recvBufFrom
     Network.Socket.Buffer.sendBufTo Network.Socket.Name.getPeerName
     Network.Socket.Name.getSocketName Network.Socket.Syscall.accept
     Network.Socket.Syscall.bind Network.Socket.Syscall.connect NetworkTypes.SockAddr
     NetworkTypes.Socket
*)

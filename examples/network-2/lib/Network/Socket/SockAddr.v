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
Require Network.Socket.Types.

(* No type declarations to convert. *)

(* Converted value declarations: *)

Definition sendBufTo {a}
   : Network.Socket.Types.Socket ->
     GHC.Ptr.Ptr a ->
     GHC.Num.Int -> Network.Socket.Types.SockAddr -> IO.IO GHC.Num.Int :=
  Network.Socket.Buffer.sendBufTo.

Definition recvBufFrom {a}
   : Network.Socket.Types.Socket ->
     GHC.Ptr.Ptr a ->
     GHC.Num.Int -> IO.IO (GHC.Num.Int * Network.Socket.Types.SockAddr)%type :=
  Network.Socket.Buffer.recvBufFrom.

Definition getSocketName
   : Network.Socket.Types.Socket -> IO.IO Network.Socket.Types.SockAddr :=
  Network.Socket.Name.getSocketName.

Definition getPeerName
   : Network.Socket.Types.Socket -> IO.IO Network.Socket.Types.SockAddr :=
  Network.Socket.Name.getPeerName.

Definition connect
   : Network.Socket.Types.Socket -> Network.Socket.Types.SockAddr -> IO.IO unit :=
  Network.Socket.Syscall.connect.

Definition bind
   : Network.Socket.Types.Socket -> Network.Socket.Types.SockAddr -> IO.IO unit :=
  Network.Socket.Syscall.bind.

Definition accept
   : Network.Socket.Types.Socket ->
     IO.IO (Network.Socket.Types.Socket * Network.Socket.Types.SockAddr)%type :=
  Network.Socket.Syscall.accept.

(* External variables:
     op_zt__ unit GHC.Num.Int GHC.Ptr.Ptr IO.IO Network.Socket.Buffer.recvBufFrom
     Network.Socket.Buffer.sendBufTo Network.Socket.Name.getPeerName
     Network.Socket.Name.getSocketName Network.Socket.Syscall.accept
     Network.Socket.Syscall.bind Network.Socket.Syscall.connect
     Network.Socket.Types.SockAddr Network.Socket.Types.Socket
*)

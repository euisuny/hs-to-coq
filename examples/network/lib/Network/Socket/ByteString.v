(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Converted imports: *)

Require Data.ByteString.Internal.
Require GHC.Num.
Require IO.
Require Network.Socket.ByteString.IO.
Require NetworkTypes.

(* No type declarations to convert. *)

(* Converted value declarations: *)

Definition sendTo
   : NetworkTypes.Socket ->
     Data.ByteString.Internal.ByteString ->
     NetworkTypes.SockAddr -> IO.IO GHC.Num.Int :=
  Network.Socket.ByteString.IO.sendTo.

Definition sendAllTo
   : NetworkTypes.Socket ->
     Data.ByteString.Internal.ByteString -> NetworkTypes.SockAddr -> IO.IO unit :=
  Network.Socket.ByteString.IO.sendAllTo.

Definition recvFrom
   : NetworkTypes.Socket ->
     GHC.Num.Int ->
     IO.IO (Data.ByteString.Internal.ByteString * NetworkTypes.SockAddr)%type :=
  Network.Socket.ByteString.IO.recvFrom.

(* External variables:
     op_zt__ unit Data.ByteString.Internal.ByteString GHC.Num.Int IO.IO
     Network.Socket.ByteString.IO.recvFrom Network.Socket.ByteString.IO.sendAllTo
     Network.Socket.ByteString.IO.sendTo NetworkTypes.SockAddr NetworkTypes.Socket
*)

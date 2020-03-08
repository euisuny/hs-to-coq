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
Require IO.
Require Network.Socket.ByteString.IO.
Require Network.Socket.Types.

(* No type declarations to convert. *)

(* Converted value declarations: *)

Definition sendTo
   : Network.Socket.Types.Socket ->
     Data.ByteString.Internal.ByteString ->
     Network.Socket.Types.SockAddr -> IO.IO GHC.Num.Int :=
  Network.Socket.ByteString.IO.sendTo.

Definition sendAllTo
   : Network.Socket.Types.Socket ->
     Data.ByteString.Internal.ByteString ->
     Network.Socket.Types.SockAddr -> IO.IO unit :=
  Network.Socket.ByteString.IO.sendAllTo.

Definition recvFrom
   : Network.Socket.Types.Socket ->
     GHC.Num.Int ->
     IO.IO (Data.ByteString.Internal.ByteString *
            Network.Socket.Types.SockAddr)%type :=
  Network.Socket.ByteString.IO.recvFrom.

(* External variables:
     op_zt__ unit Data.ByteString.Internal.ByteString GHC.Num.Int IO.IO
     Network.Socket.ByteString.IO.recvFrom Network.Socket.ByteString.IO.sendAllTo
     Network.Socket.ByteString.IO.sendTo Network.Socket.Types.SockAddr
     Network.Socket.Types.Socket
*)

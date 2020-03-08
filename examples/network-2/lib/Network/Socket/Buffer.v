(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Converted imports: *)

Require GHC.Base.
Require GHC.IO.Exception.
Require GHC.Num.
Require GHC.Ptr.
Require IO.
Require Network.Socket.Types.

(* No type declarations to convert. *)

(* Converted value declarations: *)

Axiom sendBufTo : forall {sa} {a},
                  forall `{Network.Socket.Types.SocketAddress sa},
                  Network.Socket.Types.Socket ->
                  GHC.Ptr.Ptr a -> GHC.Num.Int -> sa -> IO.IO GHC.Num.Int.

Axiom sendBuf : Network.Socket.Types.Socket ->
                GHC.Ptr.Ptr GHC.Word.Word8 -> GHC.Num.Int -> IO.IO GHC.Num.Int.

Axiom recvBufNoWait : Network.Socket.Types.Socket ->
                      GHC.Ptr.Ptr GHC.Word.Word8 -> GHC.Num.Int -> IO.IO GHC.Num.Int.

Axiom recvBufFrom : forall {sa} {a},
                    forall `{Network.Socket.Types.SocketAddress sa},
                    Network.Socket.Types.Socket ->
                    GHC.Ptr.Ptr a -> GHC.Num.Int -> IO.IO (GHC.Num.Int * sa)%type.

Axiom recvBuf : Network.Socket.Types.Socket ->
                GHC.Ptr.Ptr GHC.Word.Word8 -> GHC.Num.Int -> IO.IO GHC.Num.Int.

Axiom mkInvalidRecvArgError : GHC.Base.String -> GHC.IO.Exception.IOError.

(* External variables:
     op_zt__ GHC.Base.String GHC.IO.Exception.IOError GHC.Num.Int GHC.Ptr.Ptr
     GHC.Word.Word8 IO.IO Network.Socket.Types.Socket
     Network.Socket.Types.SocketAddress
*)

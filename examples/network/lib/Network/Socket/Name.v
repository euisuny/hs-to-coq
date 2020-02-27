(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Converted imports: *)

Require Foreign.Marshal.Utils.
Require Foreign.Storable.
Require GHC.Base.
Require GHC.IO.Exception.
Require GHC.Real.
Require IO.
Require Network.Socket.Internal.
Require Network.Socket.Types.
Require NetworkTypes.
Import GHC.Base.Notations.

(* No type declarations to convert. *)

(* Converted value declarations: *)

Definition getSocketName {sa} `{Network.Socket.Types.SocketAddress sa}
   : NetworkTypes.Socket -> IO.IO sa :=
  fun s =>
    Network.Socket.Types.withNewSocketAddress (fun ptr sz =>
                                                 Foreign.Marshal.Utils.with_ (GHC.Real.fromIntegral sz) (fun int_star =>
                                                                                                           Network.Socket.Types.withFdSocket
                                                                                                           s (fun fd =>
                                                                                                                Network.Socket.Internal.throwSocketErrorIfMinus1Retry_
                                                                                                                (GHC.Base.hs_string__
                                                                                                                 "Network.Socket.getSocketName")
                                                                                                                (c_getsockname
                                                                                                                 fd ptr
                                                                                                                 int_star)
                                                                                                                GHC.Base.>>
                                                                                                                Network.Socket.Types.peekSocketAddress
                                                                                                                ptr))).

Definition socketPort
   : NetworkTypes.Socket -> IO.IO Network.Socket.Types.PortNumber :=
  fun s =>
    getSocketName s GHC.Base.>>=
    (fun sa =>
       match sa with
       | NetworkTypes.SockAddrInet port _ => GHC.Base.return_ port
       | Network.Socket.Types.SockAddrInet6 port _ _ _ => GHC.Base.return_ port
       | _ =>
           GHC.IO.Exception.ioError (GHC.IO.Exception.userError (GHC.Base.hs_string__
                                                                 "Network.Socket.socketPort: AF_UNIX not supported."))
       end).

Definition socketPortSafe
   : NetworkTypes.Socket -> IO.IO (option Network.Socket.Types.PortNumber) :=
  fun s =>
    getSocketName s GHC.Base.>>=
    (fun sa =>
       GHC.Base.return_ (match sa with
                         | NetworkTypes.SockAddrInet port _ => Some port
                         | Network.Socket.Types.SockAddrInet6 port _ _ _ => Some port
                         | _ => None
                         end)).

Definition getPeerName {sa} `{Network.Socket.Types.SocketAddress sa}
   : NetworkTypes.Socket -> IO.IO sa :=
  fun s =>
    Network.Socket.Types.withNewSocketAddress (fun ptr sz =>
                                                 Foreign.Marshal.Utils.with_ (GHC.Real.fromIntegral sz) (fun int_star =>
                                                                                                           Network.Socket.Types.withFdSocket
                                                                                                           s (fun fd =>
                                                                                                                Network.Socket.Internal.throwSocketErrorIfMinus1Retry_
                                                                                                                (GHC.Base.hs_string__
                                                                                                                 "Network.Socket.getPeerName")
                                                                                                                (c_getpeername
                                                                                                                 fd ptr
                                                                                                                 int_star)
                                                                                                                GHC.Base.>>
                                                                                                                (Foreign.Storable.peek
                                                                                                                 int_star
                                                                                                                 GHC.Base.>>=
                                                                                                                 (fun _sz =>
                                                                                                                    Network.Socket.Types.peekSocketAddress
                                                                                                                    ptr))))).

(* External variables:
     None Some c_getpeername c_getsockname option Foreign.Marshal.Utils.with_
     Foreign.Storable.peek GHC.Base.op_zgzg__ GHC.Base.op_zgzgze__ GHC.Base.return_
     GHC.IO.Exception.ioError GHC.IO.Exception.userError GHC.Real.fromIntegral IO.IO
     Network.Socket.Internal.throwSocketErrorIfMinus1Retry_
     Network.Socket.Types.PortNumber Network.Socket.Types.SockAddrInet6
     Network.Socket.Types.SocketAddress Network.Socket.Types.peekSocketAddress
     Network.Socket.Types.withFdSocket Network.Socket.Types.withNewSocketAddress
     NetworkTypes.SockAddrInet NetworkTypes.Socket
*)

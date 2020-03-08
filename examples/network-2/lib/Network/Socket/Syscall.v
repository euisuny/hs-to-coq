(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Converted imports: *)

Require Control.Exception.Base.
Require Coq.Init.Datatypes.
Require Data.Foldable.
Require Data.Functor.
Require Foreign.C.Error.
Require Foreign.C.Types.
Require Foreign.Marshal.Utils.
Require GHC.Base.
Require GHC.Conc.IO.
Require GHC.Num.
Require GHC.Ptr.
Require GHC.Real.
Require IO.
Require Network.Socket.Fcntl.
Require Network.Socket.Internal.
Require Network.Socket.Options.
Require Network.Socket.Types.
Import Data.Functor.Notations.
Import GHC.Base.Notations.
Import GHC.Num.Notations.

(* No type declarations to convert. *)

(* Converted value declarations: *)

Definition socket
   : Network.Socket.Types.Family ->
     Network.Socket.Types.SocketType ->
     Network.Socket.Types.ProtocolNumber -> IO.IO Network.Socket.Types.Socket :=
  fun family stype protocol =>
    let unsetIPv6Only :=
      fun s =>
        GHC.Base.when (andb (family GHC.Base.== Network.Socket.Types.AF_INET6)
                            (Data.Foldable.elem stype (cons Network.Socket.Types.Stream (cons
                                                             Network.Socket.Types.Datagram nil))))
        (Network.Socket.Options.setSocketOption s Network.Socket.Options.IPv6Only #0) in
    let setNonBlock := fun fd => Network.Socket.Fcntl.setNonBlockIfNeeded fd in
    let modifyFlag := fun c_stype => c_stype in
    let create :=
      (modifyFlag Data.Functor.<$>
       Network.Socket.Types.packSocketTypeOrThrow (GHC.Base.hs_string__ "socket")
       stype) GHC.Base.>>=
      (fun c_stype =>
         Network.Socket.Internal.throwSocketErrorIfMinus1Retry (GHC.Base.hs_string__
                                                                "Network.Socket.socket") (c_socket
                                                                                          (Network.Socket.Types.packFamily
                                                                                           family) c_stype protocol)) in
    Control.Exception.Base.bracketOnError create Network.Socket.Types.c_close
    (fun fd =>
       setNonBlock fd GHC.Base.>>
       (Network.Socket.Types.mkSocket fd GHC.Base.>>=
        (fun s => unsetIPv6Only s GHC.Base.>> GHC.Base.return_ s))).

Definition listen : Network.Socket.Types.Socket -> GHC.Num.Int -> IO.IO unit :=
  fun s backlog =>
    Network.Socket.Types.withFdSocket s (fun fd =>
                                           Network.Socket.Internal.throwSocketErrorIfMinus1Retry_ (GHC.Base.hs_string__
                                                                                                   "Network.Socket.listen")
                                           (c_listen fd (GHC.Real.fromIntegral backlog))).

Definition connectLoop {sa} `{Network.Socket.Types.SocketAddress sa}
   : Network.Socket.Types.Socket ->
     GHC.Ptr.Ptr sa -> Foreign.C.Types.CInt -> IO.IO unit :=
  fun s p_sa sz =>
    let errLoc :=
      Coq.Init.Datatypes.app (GHC.Base.hs_string__ "Network.Socket.connect: ")
                             (GHC.Show.show s) in
    let connectBlocked :=
      Network.Socket.Types.withFdSocket s (GHC.Conc.IO.threadWaitWrite GHC.Base.∘
                                           GHC.Real.fromIntegral) GHC.Base.>>
      (Network.Socket.Options.getSocketOption s Network.Socket.Options.SoError
       GHC.Base.>>=
       (fun err =>
          GHC.Base.when (err GHC.Base./= #0) (Network.Socket.Internal.throwSocketErrorCode
                                              errLoc (GHC.Real.fromIntegral err)))) in
    let fix loop fd
              := c_connect fd p_sa sz GHC.Base.>>=
                 (fun r =>
                    GHC.Base.when (r GHC.Base.== GHC.Num.negate #1) (Foreign.C.Error.getErrno
                                                                     GHC.Base.>>=
                                                                     (fun err =>
                                                                        if err GHC.Base.== Foreign.C.Error.eINTR : bool
                                                                        then loop fd else
                                                                        if err GHC.Base.==
                                                                           Foreign.C.Error.eINPROGRESS : bool
                                                                        then connectBlocked else
                                                                        let '_otherwise := tt in
                                                                        Network.Socket.Internal.throwSocketError
                                                                        errLoc))) in
    Network.Socket.Types.withFdSocket s (fun fd => loop fd).

Definition connect {sa} `{Network.Socket.Types.SocketAddress sa}
   : Network.Socket.Types.Socket -> sa -> IO.IO unit :=
  fun s sa =>
    Network.Socket.Internal.withSocketsDo (Network.Socket.Types.withSocketAddress sa
                                                                                  (fun p_sa sz =>
                                                                                     connectLoop s p_sa
                                                                                     (GHC.Real.fromIntegral sz))).

Definition bind {sa} `{Network.Socket.Types.SocketAddress sa}
   : Network.Socket.Types.Socket -> sa -> IO.IO unit :=
  fun s sa =>
    Network.Socket.Types.withSocketAddress sa (fun p_sa siz =>
                                                 Data.Functor.void (Network.Socket.Types.withFdSocket s (fun fd =>
                                                                                                         let sz :=
                                                                                                           GHC.Real.fromIntegral
                                                                                                           siz in
                                                                                                         Network.Socket.Internal.throwSocketErrorIfMinus1Retry
                                                                                                         (GHC.Base.hs_string__
                                                                                                          "Network.Socket.bind")
                                                                                                         (c_bind fd p_sa
                                                                                                                 sz)))).

Definition accept {sa} `{Network.Socket.Types.SocketAddress sa}
   : Network.Socket.Types.Socket ->
     IO.IO (Network.Socket.Types.Socket * sa)%type :=
  fun listing_sock =>
    let callAccept :=
      fun fd sa sz =>
        Foreign.Marshal.Utils.with_ (GHC.Real.fromIntegral sz) (fun ptr_len =>
                                                                  Network.Socket.Internal.throwSocketErrorWaitRead
                                                                  listing_sock (GHC.Base.hs_string__
                                                                                "Network.Socket.accept") (c_accept fd sa
                                                                                                          ptr_len)
                                                                  GHC.Base.>>=
                                                                  (fun new_fd =>
                                                                     Network.Socket.Fcntl.setNonBlockIfNeeded new_fd
                                                                     GHC.Base.>>
                                                                     (Network.Socket.Fcntl.setCloseOnExecIfNeeded new_fd
                                                                      GHC.Base.>>
                                                                      GHC.Base.return_ new_fd))) in
    Network.Socket.Types.withNewSocketAddress (fun new_sa sz =>
                                                 Network.Socket.Types.withFdSocket listing_sock (fun listing_fd =>
                                                                                                   (callAccept
                                                                                                    listing_fd new_sa sz
                                                                                                    GHC.Base.>>=
                                                                                                    Network.Socket.Types.mkSocket)
                                                                                                   GHC.Base.>>=
                                                                                                   (fun new_sock =>
                                                                                                      Network.Socket.Types.peekSocketAddress
                                                                                                      new_sa
                                                                                                      GHC.Base.>>=
                                                                                                      (fun new_addr =>
                                                                                                         GHC.Base.return_
                                                                                                         (pair new_sock
                                                                                                               new_addr))))).

(* External variables:
     andb bool c_accept c_bind c_connect c_listen c_socket cons nil op_zt__ pair tt
     unit Control.Exception.Base.bracketOnError Coq.Init.Datatypes.app
     Data.Foldable.elem Data.Functor.op_zlzdzg__ Data.Functor.void
     Foreign.C.Error.eINPROGRESS Foreign.C.Error.eINTR Foreign.C.Error.getErrno
     Foreign.C.Types.CInt Foreign.Marshal.Utils.with_ GHC.Base.op_z2218U__
     GHC.Base.op_zeze__ GHC.Base.op_zgzg__ GHC.Base.op_zgzgze__ GHC.Base.op_zsze__
     GHC.Base.return_ GHC.Base.when GHC.Conc.IO.threadWaitWrite GHC.Num.Int
     GHC.Num.fromInteger GHC.Num.negate GHC.Ptr.Ptr GHC.Real.fromIntegral
     GHC.Show.show IO.IO Network.Socket.Fcntl.setCloseOnExecIfNeeded
     Network.Socket.Fcntl.setNonBlockIfNeeded
     Network.Socket.Internal.throwSocketError
     Network.Socket.Internal.throwSocketErrorCode
     Network.Socket.Internal.throwSocketErrorIfMinus1Retry
     Network.Socket.Internal.throwSocketErrorIfMinus1Retry_
     Network.Socket.Internal.throwSocketErrorWaitRead
     Network.Socket.Internal.withSocketsDo Network.Socket.Options.IPv6Only
     Network.Socket.Options.SoError Network.Socket.Options.getSocketOption
     Network.Socket.Options.setSocketOption Network.Socket.Types.AF_INET6
     Network.Socket.Types.Datagram Network.Socket.Types.Family
     Network.Socket.Types.ProtocolNumber Network.Socket.Types.Socket
     Network.Socket.Types.SocketAddress Network.Socket.Types.SocketType
     Network.Socket.Types.Stream Network.Socket.Types.c_close
     Network.Socket.Types.mkSocket Network.Socket.Types.packFamily
     Network.Socket.Types.packSocketTypeOrThrow
     Network.Socket.Types.peekSocketAddress Network.Socket.Types.withFdSocket
     Network.Socket.Types.withNewSocketAddress Network.Socket.Types.withSocketAddress
*)

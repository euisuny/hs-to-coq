Require GHC.Base.
Require GHC.Num.

Axiom Socket : Type.
Axiom SockAddr : Type.
Axiom SocketOption : Type.
Axiom HostAddress : Type.
Axiom ProtocolNumber : Type.
Axiom SocketType : Type.
Axiom Family : Type.
Axiom AF_INET : Family.
Axiom Stream : SocketType.
Axiom SockAddrInet : Num.Int -> HostAddress -> SockAddr.
Axiom ReuseAddr : SocketOption.
Axiom iNADDR_ANY : HostAddress.


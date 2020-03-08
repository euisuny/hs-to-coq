(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Preamble *)

From ITree Require Import ITree. 

(* Converted imports: *)

Require GHC.Base.
Require GHC.Num.
Require IO.
Require Network.
Require NetworkTypes.
Import GHC.Base.Notations.
Import GHC.Num.Notations.

(* No type declarations to convert. *)

(* Converted value declarations: *)

Definition runConn
   : (NetworkTypes.Socket * NetworkTypes.SockAddr)%type -> IO.IO unit :=
  fun '(pair sock _) =>
    Network.send sock (GHC.Base.hs_string__ "Hello World!") GHC.Base.>>
    Network.close sock.

Definition mainLoop : NetworkTypes.Socket -> IO.IO unit :=
  fun (sock : NetworkTypes.Socket) =>
    (@ITree.forever IO.ioE unit unit (Network.accept sock GHC.Base.>>=
      (fun conn => runConn conn))).

Definition main : IO.IO unit :=
  Network.socket NetworkTypes.AF_INET NetworkTypes.Stream #0 GHC.Base.>>=
  (fun sock =>
     Network.setSocketOption sock NetworkTypes.ReuseAddr #1 GHC.Base.>>
     (Network.bind sock (NetworkTypes.SockAddrInet #4242 NetworkTypes.iNADDR_ANY)
      GHC.Base.>>
      (Network.listen sock #2 GHC.Base.>> mainLoop sock))).

(* External variables:
     op_zt__ pair unit GHC.Base.op_zgzg__ GHC.Base.op_zgzgze__ GHC.Num.fromInteger
     IO.IO IO.ioE ITree.forever Network.accept Network.bind Network.close
     Network.listen Network.send Network.setSocketOption Network.socket
     NetworkTypes.AF_INET NetworkTypes.ReuseAddr NetworkTypes.SockAddr
     NetworkTypes.SockAddrInet NetworkTypes.Socket NetworkTypes.Stream
     NetworkTypes.iNADDR_ANY
*)

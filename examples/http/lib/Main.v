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
Require NetworkTypes.
Require Network_.
Import GHC.Base.Notations.
Import GHC.Num.Notations.

(* No type declarations to convert. *)

(* Converted value declarations: *)

Definition runConn : (IO.Socket * NetworkTypes.SockAddr)%type -> IO.IO unit :=
  fun '(pair sock _) =>
    Network_.send sock (GHC.Base.hs_string__ "Hello World!") GHC.Base.>>
    Network_.close sock.

Definition mainLoop : IO.Socket -> IO.IO unit :=
  fun (sock : IO.Socket) =>
    (@ITree.forever IO.haskE unit unit (Network_.accept sock GHC.Base.>>=
      (fun conn => runConn conn))).

Definition main : IO.IO unit :=
  Network_.socket NetworkTypes.AF_INET NetworkTypes.Stream #0 GHC.Base.>>=
  (fun sock =>
     Network_.setSocketOption sock NetworkTypes.ReuseAddr #1 GHC.Base.>>
     (Network_.bind sock (NetworkTypes.SockAddrInet #4242 NetworkTypes.iNADDR_ANY)
      GHC.Base.>>
      (Network_.listen sock #2 GHC.Base.>> mainLoop sock))).

(* External variables:
     op_zt__ pair unit GHC.Base.op_zgzg__ GHC.Base.op_zgzgze__ GHC.Num.fromInteger
     IO.IO IO.Socket IO.haskE ITree.forever NetworkTypes.AF_INET
     NetworkTypes.ReuseAddr NetworkTypes.SockAddr NetworkTypes.SockAddrInet
     NetworkTypes.Stream NetworkTypes.iNADDR_ANY Network_.accept Network_.bind
     Network_.close Network_.listen Network_.send Network_.setSocketOption
     Network_.socket
*)

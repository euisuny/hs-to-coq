(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Converted imports: *)

Require Data.Bits.
Require Foreign.C.Types.
Require GHC.Base.
Require GHC.Num.
Require IO.
Require Network.Socket.Cbits.
Require System.Posix.Internals.
Import Data.Bits.Notations.
Import GHC.Base.Notations.
Import GHC.Num.Notations.

(* No type declarations to convert. *)

(* Converted value declarations: *)

Definition setNonBlockIfNeeded : Foreign.C.Types.CInt -> IO.IO unit :=
  fun fd => System.Posix.Internals.setNonBlockingFD fd true.

Definition setCloseOnExecIfNeeded : Foreign.C.Types.CInt -> IO.IO unit :=
  fun fd => System.Posix.Internals.setCloseOnExec fd.

Definition getNonBlock : Foreign.C.Types.CInt -> IO.IO bool :=
  fun fd =>
    c_fcntl_read fd Network.Socket.Cbits.fGetFl #0 GHC.Base.>>=
    (fun flags =>
       let ret := flags Data.Bits..&.(**) Network.Socket.Cbits.oNonBlock in
       GHC.Base.return_ (ret GHC.Base./= #0)).

Definition getCloseOnExec : Foreign.C.Types.CInt -> IO.IO bool :=
  fun fd =>
    c_fcntl_read fd Network.Socket.Cbits.fGetFd #0 GHC.Base.>>=
    (fun flags =>
       let ret := flags Data.Bits..&.(**) Network.Socket.Cbits.fdCloexec in
       GHC.Base.return_ (ret GHC.Base./= #0)).

(* External variables:
     bool c_fcntl_read true unit Data.Bits.op_zizazi__ Foreign.C.Types.CInt
     GHC.Base.op_zgzgze__ GHC.Base.op_zsze__ GHC.Base.return_ GHC.Num.fromInteger
     IO.IO Network.Socket.Cbits.fGetFd Network.Socket.Cbits.fGetFl
     Network.Socket.Cbits.fdCloexec Network.Socket.Cbits.oNonBlock
     System.Posix.Internals.setCloseOnExec System.Posix.Internals.setNonBlockingFD
*)

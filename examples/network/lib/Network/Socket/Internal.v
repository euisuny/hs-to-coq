(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Converted imports: *)

Require Data.Functor.
Require Foreign.C.Error.
Require Foreign.C.Types.
Require GHC.Base.
Require GHC.Conc.IO.
Require GHC.IO.Exception.
Require GHC.Num.
Require GHC.Real.
Require IO.
Require Network.Socket.Types.
Require NetworkTypes.

(* No type declarations to convert. *)

(* Converted value declarations: *)

Definition withSocketsDo {a} : IO.IO a -> IO.IO a :=
  fun x => x.

Definition throwSocketErrorIfMinus1_ {a} `{GHC.Base.Eq_ a} `{GHC.Num.Num a}
   : GHC.Base.String -> IO.IO a -> IO.IO unit :=
  Foreign.C.Error.throwErrnoIfMinus1_.

Definition throwSocketErrorIfMinus1RetryMayBlock {a} {b} `{GHC.Base.Eq_ a}
  `{GHC.Num.Num a}
   : GHC.Base.String -> IO.IO b -> IO.IO a -> IO.IO a :=
  fun name on_block act =>
    Foreign.C.Error.throwErrnoIfMinus1RetryMayBlock name act on_block.

Definition throwSocketErrorWaitRead {a} `{GHC.Base.Eq_ a} `{GHC.Num.Num a}
   : NetworkTypes.Socket -> GHC.Base.String -> IO.IO a -> IO.IO a :=
  fun s name io =>
    Network.Socket.Types.withFdSocket s (fun fd =>
                                           throwSocketErrorIfMinus1RetryMayBlock name (GHC.Conc.IO.threadWaitRead
                                                                                       (GHC.Real.fromIntegral fd)) io).

Definition throwSocketErrorWaitWrite {a} `{GHC.Base.Eq_ a} `{GHC.Num.Num a}
   : NetworkTypes.Socket -> GHC.Base.String -> IO.IO a -> IO.IO a :=
  fun s name io =>
    Network.Socket.Types.withFdSocket s (fun fd =>
                                           throwSocketErrorIfMinus1RetryMayBlock name (GHC.Conc.IO.threadWaitWrite
                                                                                       (GHC.Real.fromIntegral fd)) io).

Definition throwSocketErrorIfMinus1Retry {a} `{GHC.Base.Eq_ a} `{GHC.Num.Num a}
   : GHC.Base.String -> IO.IO a -> IO.IO a :=
  Foreign.C.Error.throwErrnoIfMinus1Retry.

Definition throwSocketErrorIfMinus1Retry_ {a} `{GHC.Base.Eq_ a} `{GHC.Num.Num a}
   : GHC.Base.String -> IO.IO a -> IO.IO unit :=
  fun loc m => Data.Functor.void (throwSocketErrorIfMinus1Retry loc m).

Definition throwSocketErrorCode {a}
   : GHC.Base.String -> Foreign.C.Types.CInt -> IO.IO a :=
  fun loc errno =>
    GHC.IO.Exception.ioError (Foreign.C.Error.errnoToIOError loc
                              (Foreign.C.Error.Errno errno) None None).

Definition throwSocketError {a} : GHC.Base.String -> IO.IO a :=
  Foreign.C.Error.throwErrno.

(* External variables:
     None unit Data.Functor.void Foreign.C.Error.Errno Foreign.C.Error.errnoToIOError
     Foreign.C.Error.throwErrno Foreign.C.Error.throwErrnoIfMinus1Retry
     Foreign.C.Error.throwErrnoIfMinus1RetryMayBlock
     Foreign.C.Error.throwErrnoIfMinus1_ Foreign.C.Types.CInt GHC.Base.Eq_
     GHC.Base.String GHC.Conc.IO.threadWaitRead GHC.Conc.IO.threadWaitWrite
     GHC.IO.Exception.ioError GHC.Num.Num GHC.Real.fromIntegral IO.IO
     Network.Socket.Types.withFdSocket NetworkTypes.Socket
*)

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
Require Data.Functor.
Require Foreign.C.Types.
Require Foreign.Marshal.Alloc.
Require GHC.Base.
Require GHC.Conc.IO.
Require GHC.Err.
Require GHC.Event.Internal.
Require GHC.Event.Manager.
Require GHC.Event.Thread.
Require GHC.Event.TimerManager.
Require GHC.MVar.
Require GHC.Num.
Require IO.
Require Network.Socket.Buffer.
Require Network.Socket.Internal.
Require Network.Socket.Types.
Require System.Posix.Types.
Import GHC.Base.Notations.
Import GHC.Num.Notations.

(* Converted type declarations: *)

Inductive Wait : Type := | MoreData : Wait |  TimeoutTripped : Wait.

Inductive ShutdownCmd : Type
  := | ShutdownReceive : ShutdownCmd
  |  ShutdownSend : ShutdownCmd
  |  ShutdownBoth : ShutdownCmd.

Instance Default__Wait : GHC.Err.Default Wait :=
  GHC.Err.Build_Default _ MoreData.

Instance Default__ShutdownCmd : GHC.Err.Default ShutdownCmd :=
  GHC.Err.Build_Default _ ShutdownReceive.

(* Converted value declarations: *)

Definition sdownCmdToInt : ShutdownCmd -> Foreign.C.Types.CInt :=
  fun arg_0__ =>
    match arg_0__ with
    | ShutdownReceive => #0
    | ShutdownSend => #1
    | ShutdownBoth => #2
    end.

Definition shutdown
   : Network.Socket.Types.Socket -> ShutdownCmd -> IO.IO unit :=
  fun s stype =>
    Data.Functor.void (Network.Socket.Types.withFdSocket s (fun fd =>
                                                            Network.Socket.Internal.throwSocketErrorIfMinus1Retry_
                                                            (GHC.Base.hs_string__ "Network.Socket.shutdown") (c_shutdown
                                                                                                              fd
                                                                                                              (sdownCmdToInt
                                                                                                               stype)))).

Definition gracefulClose
   : Network.Socket.Types.Socket -> GHC.Num.Int -> IO.IO unit :=
  fun s tmout =>
    let bufSize := #1024 in
    let unregister :=
      fun arg_1__ arg_2__ arg_3__ =>
        match arg_1__, arg_2__, arg_3__ with
        | evmgr, tmmgr, pair key1 key2 =>
            GHC.Event.TimerManager.unregisterTimeout tmmgr key1 GHC.Base.>>
            GHC.Event.Manager.unregisterFd evmgr key2
        end in
    let register :=
      fun evmgr tmmgr mvar =>
        GHC.Event.TimerManager.registerTimeout tmmgr (tmout GHC.Num.* #1000)
        (GHC.MVar.putMVar mvar TimeoutTripped) GHC.Base.>>=
        (fun key1 =>
           Network.Socket.Types.withFdSocket s (fun fd' =>
                                                  let fd := System.Posix.Types.Fd fd' in
                                                  let callback :=
                                                    fun arg_7__ arg_8__ => GHC.MVar.putMVar mvar MoreData in
                                                  GHC.Event.Manager.registerFd evmgr callback fd
                                                  GHC.Event.Internal.evtRead GHC.Event.Internal.OneShot) GHC.Base.>>=
           (fun key2 => GHC.Base.return_ (pair key1 key2))) in
    let recvEOFev :=
      fun evmgr =>
        GHC.Event.Thread.getSystemTimerManager GHC.Base.>>=
        (fun tmmgr =>
           GHC.MVar.newEmptyMVar GHC.Base.>>=
           (fun mvar =>
              Control.Exception.Base.bracket (register evmgr tmmgr mvar) (unregister evmgr
                                              tmmgr) (fun arg_13__ =>
                                                        GHC.MVar.takeMVar mvar GHC.Base.>>=
                                                        (fun wait =>
                                                           match wait with
                                                           | TimeoutTripped => GHC.Base.return_ tt
                                                           | MoreData =>
                                                               Control.Exception.Base.bracket
                                                               (Foreign.Marshal.Alloc.mallocBytes bufSize)
                                                               Foreign.Marshal.Alloc.free (fun buf =>
                                                                                             Data.Functor.void
                                                                                             (Network.Socket.Buffer.recvBufNoWait
                                                                                              s buf bufSize))
                                                           end)))) in
    let clock := #200 in
    let recvEOFloop :=
      let fix loop delay buf
                := Network.Socket.Buffer.recvBufNoWait s buf bufSize GHC.Base.>>=
                   (fun r =>
                      let delay' := delay GHC.Num.+ clock in
                      GHC.Base.when (andb (r GHC.Base.== GHC.Num.negate #1) (delay' GHC.Base.< tmout))
                      (GHC.Conc.IO.threadDelay (clock GHC.Num.* #1000) GHC.Base.>>
                       loop delay' buf)) in
      Control.Exception.Base.bracket (Foreign.Marshal.Alloc.mallocBytes bufSize)
                                     Foreign.Marshal.Alloc.free (loop #0) in
    let sendRecvFIN :=
      shutdown s ShutdownSend GHC.Base.>>
      (GHC.Event.Thread.getSystemEventManager GHC.Base.>>=
       (fun mevmgr =>
          match mevmgr with
          | None => recvEOFloop
          | Some evmgr => recvEOFev evmgr
          end)) in
    Control.Exception.Base.finally sendRecvFIN (Network.Socket.Types.close s).

(* External variables:
     None Some andb c_shutdown pair tt unit Control.Exception.Base.bracket
     Control.Exception.Base.finally Data.Functor.void Foreign.C.Types.CInt
     Foreign.Marshal.Alloc.free Foreign.Marshal.Alloc.mallocBytes GHC.Base.op_zeze__
     GHC.Base.op_zgzg__ GHC.Base.op_zgzgze__ GHC.Base.op_zl__ GHC.Base.return_
     GHC.Base.when GHC.Conc.IO.threadDelay GHC.Err.Build_Default GHC.Err.Default
     GHC.Event.Internal.OneShot GHC.Event.Internal.evtRead
     GHC.Event.Manager.registerFd GHC.Event.Manager.unregisterFd
     GHC.Event.Thread.getSystemEventManager GHC.Event.Thread.getSystemTimerManager
     GHC.Event.TimerManager.registerTimeout GHC.Event.TimerManager.unregisterTimeout
     GHC.MVar.newEmptyMVar GHC.MVar.putMVar GHC.MVar.takeMVar GHC.Num.Int
     GHC.Num.fromInteger GHC.Num.negate GHC.Num.op_zp__ GHC.Num.op_zt__ IO.IO
     Network.Socket.Buffer.recvBufNoWait
     Network.Socket.Internal.throwSocketErrorIfMinus1Retry_
     Network.Socket.Types.Socket Network.Socket.Types.close
     Network.Socket.Types.withFdSocket System.Posix.Types.Fd
*)

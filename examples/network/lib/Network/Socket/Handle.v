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
Require GHC.IO.Device.
Require GHC.IO.Exception.
Require GHC.IO.Handle.
Require GHC.IO.Handle.FD.
Require GHC.IO.Handle.Types.
Require GHC.IO.IOMode.
Require IO.
Require Network.Socket.Types.
Require NetworkTypes.
Import GHC.Base.Notations.

(* No type declarations to convert. *)

(* Converted value declarations: *)

Definition socketToHandle
   : NetworkTypes.Socket ->
     GHC.IO.IOMode.IOMode -> IO.IO GHC.IO.Handle.Types.Handle :=
  fun s mode =>
    let err :=
      fun arg_0__ =>
        GHC.IO.Exception.ioError (GHC.IO.Exception.userError
                                  "socketToHandle: socket is no longer valid") in
    Network.Socket.Types.invalidateSocket s err (fun oldfd =>
                                                   GHC.IO.Handle.FD.fdToHandle' oldfd (Some GHC.IO.Device.Stream) true
                                                   (GHC.Show.show s) mode true GHC.Base.>>=
                                                   (fun h =>
                                                      GHC.IO.Handle.hSetBuffering h GHC.IO.Handle.Types.NoBuffering
                                                      GHC.Base.>>
                                                      GHC.Base.return_ h)).

(* External variables:
     Some true GHC.Base.op_zgzg__ GHC.Base.op_zgzgze__ GHC.Base.return_
     GHC.IO.Device.Stream GHC.IO.Exception.ioError GHC.IO.Exception.userError
     GHC.IO.Handle.hSetBuffering GHC.IO.Handle.FD.fdToHandle'
     GHC.IO.Handle.Types.Handle GHC.IO.Handle.Types.NoBuffering GHC.IO.IOMode.IOMode
     GHC.Show.show IO.IO Network.Socket.Types.invalidateSocket NetworkTypes.Socket
*)

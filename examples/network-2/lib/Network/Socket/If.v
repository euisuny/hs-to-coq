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
Require Foreign.C.String.
Require Foreign.Marshal.Alloc.
Require GHC.Base.
Require GHC.Num.
Require GHC.Ptr.
Require GHC.Real.
Require IO.
Import Data.Functor.Notations.
Import GHC.Base.Notations.
Import GHC.Num.Notations.

(* No type declarations to convert. *)

(* Converted value declarations: *)

Definition ifNameToIndex : GHC.Base.String -> IO.IO (option GHC.Num.Int) :=
  fun ifname =>
    Foreign.C.String.withCString ifname c_if_nametoindex GHC.Base.>>=
    (fun index =>
       GHC.Base.return_ (if index GHC.Base.== #0 : bool
                         then None
                         else Some (GHC.Real.fromIntegral index))).

Definition ifIndexToName : GHC.Num.Int -> IO.IO (option GHC.Base.String) :=
  fun ifn =>
    Foreign.Marshal.Alloc.allocaBytes #16 (fun ptr =>
                                             c_if_indextoname (GHC.Real.fromIntegral ifn) ptr GHC.Base.>>=
                                             (fun r =>
                                                if r GHC.Base.== GHC.Ptr.nullPtr : bool
                                                then GHC.Base.return_ None
                                                else Some Data.Functor.<$> Foreign.C.String.peekCString ptr)).

(* External variables:
     None Some bool c_if_indextoname c_if_nametoindex option Data.Functor.op_zlzdzg__
     Foreign.C.String.peekCString Foreign.C.String.withCString
     Foreign.Marshal.Alloc.allocaBytes GHC.Base.String GHC.Base.op_zeze__
     GHC.Base.op_zgzgze__ GHC.Base.return_ GHC.Num.Int GHC.Num.fromInteger
     GHC.Ptr.nullPtr GHC.Real.fromIntegral IO.IO
*)

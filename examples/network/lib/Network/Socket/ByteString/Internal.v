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
Require GHC.IO.Exception.
Require System.IO.Error.

(* No type declarations to convert. *)

(* Converted value declarations: *)

Definition mkInvalidRecvArgError
   : GHC.Base.String -> GHC.IO.Exception.IOError :=
  fun loc =>
    System.IO.Error.ioeSetErrorString (System.IO.Error.mkIOError
                                       GHC.IO.Exception.InvalidArgument loc None None) (GHC.Base.hs_string__
                                                                                        "non-positive length").

(* External variables:
     None GHC.Base.String GHC.IO.Exception.IOError GHC.IO.Exception.InvalidArgument
     System.IO.Error.ioeSetErrorString System.IO.Error.mkIOError
*)

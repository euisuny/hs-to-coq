(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Converted imports: *)

Require Foreign.C.Types.
Require GHC.Num.

(* No type declarations to convert. *)

(* Converted value declarations: *)

Axiom oNonBlock : Foreign.C.Types.CInt.

Axiom maxListenQueue : GHC.Num.Int.

Axiom fdCloexec : Foreign.C.Types.CInt.

Axiom fGetFl : Foreign.C.Types.CInt.

Axiom fGetFd : Foreign.C.Types.CInt.

(* External variables:
     Foreign.C.Types.CInt GHC.Num.Int
*)

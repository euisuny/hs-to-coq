(* This file gathers and reexports various definitions.
   See [Lib.LinearSpec_Interface] for a high-level overview of
   these components.
 *)

From DeepWeb Require Export
     Lib.LinearSpec_Server
     Lib.LinearSpec_Observer
     Lib.LinearSpec_Scramble
     Lib.LinearSpec_Descramble
     Lib.LinearSpec_Traces
     Lib.LinearSpec_Refinement
     Lib.LinearSpec_ServerTrace
     Lib.LinearSpec_NetworkModel.

From DeepWeb Require Import
     Lib.LinearSpec_ScrambleTransitivity.

Module Export ScramblingFacts :=
  LinearSpec_Scramble.ScramblingFacts
    LinearSpec_ScrambleTransitivity.TransitivityProof.

Module Export Refinement :=
  LinearSpec_Refinement.Refinement ScramblingFacts.

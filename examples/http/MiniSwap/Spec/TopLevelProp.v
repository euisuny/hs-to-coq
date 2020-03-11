(** * The top-level correctness property. *)

From DeepWeb Require Import
     Free.Monad.Free
     Lib.LinearSpec
     Lib.NetworkAdapter
     Spec.Swap_LinearSpec.

From DeepWeb.Spec.Vst Require Import
     MainInit
     Gprog
     SocketSpecs.

Import TracePred.

Definition ext_behavior p t := semax_prog_ext p t Vprog Gprog.

(* Difference from paper:
   [simplify_network] converts an itree over [socketE] to one that is
   over [implE]; events are mostly mapped one-to-one.
 *)
Definition swap_server_correct :=
  exists (impl_model : itree socketE unit),
    network_refines (simplify_network impl_model) real_swap_spec
    /\ ext_behavior prog impl_model.

(* Notes:
   - [tree] will be instantiated with the intermediate "C-like"
     interaction tree found in Swap_ImplModel.v
   - [simplify_network] translates between two different variants of
     the network effect type (the Vst proofs use a richer variant with
     Shutdown and Listen events, which are not yet considered by our
     high-level spec).
   - [network_refines] is "refinement modulo reordering by the
     network".
   - [semax_prog_ext] is the Vst property for Valid Hoare triples
   - [prog] is the C program (as a CompCert AST: it is imported from
     MainInit.v, which gets it from main.v)
   - [Vprog] is the set of variables for [prog]
   - [Gprog] is the function specifications for prog

  The proof of this theorem can be found in [Proofs.TopLevelProof]. *)



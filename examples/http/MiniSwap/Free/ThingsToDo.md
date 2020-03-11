Contributions
=============================
  - a cheap monad of traces
      - (terminology: not "traces"; better "computation trees" or
        "behaviors" or...
      - discuss relation to Freer monad and other monadic accounts of
        effects (resumption monad, Andreas Lockbihler's stuff, ...)
      - remark about the transformation to strictly positive form (for
        Coq) that motivated our version (whereas Freer monads were for
        performance)
           - to what extent is the form of our definition motivated by
             restrictions of Coq?  to what extent is it "natural"?
      - tau needed to satisfy termination checker (could this all be
        done without tau in Isabelle?)
           - we could drop tau in favor of adding a distinguished
             visible event (thus making our account closer to that of
             other people).  what are the pros and cons?
      - discuss choice of how we implement bind (does it introduce tau
        or not) -- one is more convenient to use
      - why coinductive?  (why not just pass fuel everywhere?)  the
        coinductive way is more natural, but does it actually change
        anything fundamental?

  - basic metatheory [OK]
      - proof that is is a "monad" (up to observational equivalence)

  - idioms for testing
      - the trick of zipping programs with specs
      - arbitrary
      - ambiguous choice operator
      - support for extraction
           - (can we extract in such a way that the taus need not be
             manifested?)

  - the fact that we can support both testing and verification with
    the same specs
      - ** why is this challenging?  if we only cared about one or the
        other, what would we do differently?
      - we verify our test monad (i.e., show that, if all tests pass,
        then the spec is true) using the infrastructure of QuickChick

  - extend to concurrent systems and specs; show and compare two
    approaches to linearizability (prove equivalence)
  - talk about the DeepWeb server
      - ideally, the Coq library that we talk about here is also
        literally used as the basis for DeepWeb
  - talk about relation to what others like the MIT group are doing in
    this space

Reading
=====================

Wiegley's work on Fiat / bytestring / refinement, Haskell 17

"Freer Monads, More Extensible Effects", Oleg Kiselyov, Hiromi Ishii.

@inproceedings{plotkin2001adequacy, title={Adequacy for algebraic
  effects}, author={Plotkin, Gordon and Power, John},
  booktitle={Foundations of Software Science and Computation
  Structures}, pages={1--24}, year={2001}, organization={Springer} }
  https://www.era.lib.ed.ac.uk/bitstream/handle/1842/187/Op_Sem_Comp_Lam.pdf?sequence=1

@inproceedings{johann2010generic, title={A generic operational
  metatheory for algebraic effects}, author={Johann, Patricia and
  Simpson, Alex and Voigtländer, Janis}, booktitle={Logic in
  Computer Science (LICS), 2010 25th Annual IEEE Symposium on},
  pages={209--218}, year={2010}, organization={IEEE} }
  http://strathprints.strath.ac.uk/34343/1/genpar.pdf


Things to do...
========================

Tidying:
     - Fix broken proofs
     - Figure out how to display traces better when
       backtracking (maybe with indentation?)
     - We probably want a parsec-like interpretation of 'or', which
       commits to the first branch if it consumes anything
     - Improve the handling of symbolic references to earlier result
       values
         - Generate and shrink request sequences all at once
         - Only generate references to BOUND symbols (from earlier
           requests)
         - Sometimes shrink references to smaller (bound) ones
     - Replace GET/PUT with logging all history (do we still think
       this is a good idea?)

Larger things:
     - prove that spec is the same as spec2 in Examples.v
     - State machines vs coinductive monadic things -- make an
       explicit connection!  (In progress)
     - Show that our thing is equivalent to linearization (what does
       this look like, exactly?)
     - Integrate with the DeepWeb server
     - Clean all this up and think about an abstract interface for it

Lower priority / more speculative:
     - Use dependent types in generation
        - Index the type of Tests by, for example, the set of etags
          that have been seen (or a numeric bound on the biggest one,
          or)
        - Index properties by the type of test that they generate
        - What about shrinking??
     - Consider adding a "stabilize / wait for responses" event so
       that we can do something about "liveness"
     - Translate the Dropbox spec to this framework
     - What we'd really like is to be able to shrink nested foralls
        - e.g., maybe do this by defining a representation for test
          cases and being able to ask a generator whether some test
          matches its internal structure (so a generator, instead of
          just returning things, can will take an existing test and,
          if it is able, shrink it).  Li-Yao is thinking about this.

Points to think about...
     - See if the MIT or Yale folks have done something similar
     - Who else out there may have done similar things?
     - One potential contribution of this stuff is the ability to use
       the same specification for both testing and verification.  How
       can we convincingly evaluate whether we've succeeded in the
       latter?

Comparison of state machines vs. traces:
  - They seem to be equivalent in expressiveness (given that we
    distinguish between input and output states).
  - SMs are simpler, more familiar, and more pedestrian (and require
    less Coq trickery)
  - Traces are easier to "program" because there is no need to
    "capture the computational state" as a data structure between
    steps.  (Cf. event loops vs. concurrent processes.)
  - Traces may be easier to compose because there is no need to fiddle
    with existential types.
  - SMs can be extended to states with decidable equality, Showable
    states, ...  May be easier to debug / visualize.
  - SMs connect naturally to VST.  (According to Nicolas and Yao. Is
    this still true for the SMs that distinguish I and O states?)

Notes about [M]
============================

What are we trying to do actually?
  - Give high-level semantics `S` to low-level programs:
    a relation `Prg -> S -> Prop`.
    Could we also test the relation before verifying it?
  - Given a semantics `s : S`, check (verify/test) it
    against a specification `S -> Prop/Checker`.

  - Testing vs Verification

So far this `S = M E X` representation seems most promising.
  - Other representations have difficult termination problems
    + Free (Haskell's conventional one)
    + As functions: Church, Van Laarhoven, mtl-style
  - Difference between CoInductive/Inductive?
    + Inductive could disallow `spin` (minor win?).
    + Tau vs fuel?
      Tau seems it can be more uniformly handled with other
      details such as ordering of non-deterministic branches.
    + Inductive+fuel sounds like the approach advocated by
      "Type Soundness Proofs with Definitional Interpreters",
      Nada Amin, Tiark Rompf, POPL'17; different motivations.
    + But coinductive semantics seem really well suited to
      long-lived servers.
  - Recursive monadic definitions seem like a
    general problem in verification with Coq.
    + We don't want to break abstractions, but then
      we cannot distinguish:
      * `bad  x = ret x >>= bad`
      * `good x = f   x >>= good`
      where f is productive.
    + Joachim's ideas about `unsafeFix` seem relevant.

Trace semantics for interaction trees
=====================================

A tree can be mapped to a set of traces, and this mapping is not injective. But
it seems our network-level semantics cannot distinguish between trees with the
same traces.

The difference might affect how we specify and prove things. It may be more difficult
to prove refinement with an abstract model that makes internal choices too early.

Monadic effects in Coq
======================

Structure
---------

- `Monad/Free.v`: Free monad definition
- `Monad/Verif.v`: Free monad theory (proof that `M` is a monad)
- `Monad/Common.v`: Common effects
- `Monad/Spec.v`: "Specification monad"
- `Monad/Concurrent.v`: Modelling concurrency
- `Monad/StateMachine.v`, `Monad/IO.v`, `Examples.v`:
  Examples of use of the free monad for specifications and testing.
- `Prelim.v`: Toolbox

Dependencies
------------

Skip this if you can already build the DeepWeb repo.

### Recommended

- opam
- OCaml (4.04)
- Coq (8.6)

### coq-ext-lib

```
opam repo add coq-released https://coq.inria.fr/opam/released
opam install coq-ext-lib
```

### QuickChick

```
git clone -b trunk https://github.com/QuickChick/QuickChick.git
cd QuickChick
make && make install
```

Build
-----

```
make
```

Running tests
-------------

(Hackish)

QuickChick and Coq currently have trouble with modular project architectures,
so the command `QuickChick my_spec.` doesn't work.

Instead, inside `Examples.v`, define the checker under test
`the_spec : Checker` and run this in the command line:

```
make run
```

Output:

```
(...)
+++ Passed 10000 tests (0 discards)
```

The script `qc-fix` contains more information about the hack.

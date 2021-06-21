Release notes for Agda version 2.6.3
====================================

Language
--------

* The new option `--erased-cubical` turns on a variant of Cubical Agda
  (see [#4701](https://github.com/agda/agda/issues/4701)).

  When this variant of Cubical Agda is used glue (and some related
  builtins) may only be used in erased settings, and higher
  constructors must be erased. One can import regular Cubical Agda
  code from this variant of Cubical Agda, but names defined using
  Cubical Agda are (mostly) treated as if they had been marked as
  erased. See the [reference
  manual](https://agda.readthedocs.io/en/latest/language/cubical.html#cubical-agda-with-erased-glue-and-erased-higher-constructors)
  for more details.

  The GHC and JS backends can compile code that uses
  `--erased-cubical` if the top-level module uses this flag.

  This feature is experimental.

* The cubical interval `I` now belongs to its own sort, `IUniv`, rather
  than `SSet`. For `J : ISet` and `A : J → Set l`, we have
  `(j : J) → A : Set l`, that is, the type of functions from a type in `ISet`
  to a fibrant type is fibrant.

Compiler backends
-----------------

* Both the GHC and JS backends now refuse to compile code that uses
  `--cubical`.

  Note that support for compiling code that uses `--erased-cubical`
  has been added to both backends (see above).

* The new option `--ghc-strict-data`, which is inspired by the GHC
  language extension `StrictData`, makes the GHC backend compile
  inductive data and record constructors to constructors with strict
  arguments.

  This does not apply to certain builtin types—lists, the maybe type,
  and some types related to reflection—and might not apply to types
  with `COMPILE GHC … = data …` pragmas.

* The new option `--ghc-strict`, which is inspired by the GHC language
  extension `Strict`, makes the GHC backend generate mostly strict
  code.

  Functions might not be strict in unused arguments.

  Function definitions coming from `COMPILE GHC` pragmas are not
  affected.

  This flag implies `--ghc-strict-data`, and the exceptions of that
  flag applies to this flag as well.

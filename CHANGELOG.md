Release notes for Agda version 2.6.2.1
======================================

Installation and infrastructure
-------------------------------

Agda 2.6.2.1 is expected to build with GHC versions 8.0 to 9.2.
It has been tested with the latest minor version releases of GHC for
each of these major versions:

  - 8.0.2
  - 8.2.2
  - 8.4.4
  - 8.6.5
  - 8.8.4
  - 8.10.7: Issue [#5539](https://github.com/agda/agda/issues/5539).
  - 9.0.1
  - 9.2.1:
    Issue [#5442](https://github.com/agda/agda/issues/5442),
    stackage issue [#6318](https://github.com/commercialhaskell/stackage/pull/6318).

Agda 2.6.2.1 has been adapted to recent changes in the Haskell ecosystem, including:

  - `Cabal-3.6.2`
  - `aeson-2.0`:
    Issue [#5593](https://github.com/agda/agda/issues/5593),
    stackage issue [#6217](https://github.com/commercialhaskell/stackage/issues/6217).
  - `hashable-1.4`:
    Stackage issue [#6268](https://github.com/commercialhaskell/stackage/issues/6268).
  - `transformers-0.6`

Language
--------

* The new option `--erased-cubical` turns on a variant of Cubical Agda
  (see [#4701](https://github.com/agda/agda/issues/4701)).

  When this variant of Cubical Agda is used glue (and some related
  builtins) may only be used in erased settings. One can import
  regular Cubical Agda code from this variant of Cubical Agda, but
  names defined using Cubical Agda are (mostly) treated as if they had
  been marked as erased. See the [reference
  manual](https://agda.readthedocs.io/en/latest/language/cubical.html#cubical-agda-with-erased-glue-and-erased-higher-constructors)
  for more details.

  The GHC and JS backends can compile code that uses
  `--erased-cubical` if the top-level module uses this flag.

  This feature is experimental and should be used with the
  [development version of Agda](https://github.com/agda/agda).

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

  This feature is experimental and should be used with the
  [development version of Agda](https://github.com/agda/agda).

* The new option `--ghc-strict`, which is inspired by the GHC language
  extension `Strict`, makes the GHC backend generate mostly strict
  code.

  Functions might not be strict in unused arguments.

  Function definitions coming from `COMPILE GHC` pragmas are not
  affected.

  This flag implies `--ghc-strict-data`, and the exceptions of that
  flag applies to this flag as well.

  Note that this option requires the use of GHC 9 or later.

  This feature is experimental and should be used with the
  [development version of Agda](https://github.com/agda/agda).


* JS backend now uses the native `BigInt` instead of the
  [biginteger.js](https://github.com/silentmatt/javascript-biginteger).
  Fixes [#4878](https://github.com/agda/agda/issues/4878).

LaTeX backend
-------------

* Files `agda.sty` and `postprocess-latex.pl` are now found in the `latex/`
  subdirectory of the Agda data directory (`agda --print-agda-dir`).

* `agda.sty` is now versioned (printed to the `.log` file by `latex`)
  (see [#5473](https://github.com/agda/agda/issues/5473)).

* Italics correction (inserted by `\textit` e.g. in `\AgdaBound`) now works,
  thanks to moving the `\textcolor` wrapping to the outside in `agda.sty`
  (see [#5471](https://github.com/agda/agda/issues/5471)).

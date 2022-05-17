Release notes for Agda version 2.6.2.1
======================================

Highlights
----------

* Agda 2.6.2.1 catches up to changes in the Haskell ecosystem
  (GHC 9.2.1, `aeson-2.0`, `hashable-1.4.`).

* Fixes some regressions introduced in 2.6.1:
  [#5283](https://github.com/agda/agda/issues/5283)
  [#5506](https://github.com/agda/agda/issues/5506)
  [#5610](https://github.com/agda/agda/issues/5610)

* Fixes some regressions introduced in 2.6.2:
  [#5508](https://github.com/agda/agda/issues/5508)
  [#5544](https://github.com/agda/agda/issues/5544)
  [#5565](https://github.com/agda/agda/issues/5565)
  [#5584](https://github.com/agda/agda/issues/5584)
  [#5620](https://github.com/agda/agda/issues/5620)
  [#5638](https://github.com/agda/agda/issues/5638)
  [#5657](https://github.com/agda/agda/issues/5657)

* Improvements to the compiler backends (see below).

* Feature preview: `--ghc-strict`.

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

Compiler backends
-----------------

* Both the GHC and JS backends now refuse to compile code that uses
  `--cubical`.

* The new option `--ghc-strict-data`, which is inspired by the GHC
  language extension `StrictData`, makes the GHC backend compile
  inductive data and record constructors to constructors with strict
  arguments.

  This does not apply to certain builtin types—lists, the maybe type,
  and some types related to reflection—and might not apply to types
  with `COMPILE GHC … = data …` pragmas.

  This feature is experimental.

* The new option `--ghc-strict`, which is inspired by the GHC language
  extension `Strict`, makes the GHC backend generate mostly strict
  code.

  Functions might not be strict in unused arguments.

  Function definitions coming from `COMPILE GHC` pragmas are not
  affected.

  This flag implies `--ghc-strict-data`, and the exceptions of that
  flag applies to this flag as well.

  Note that this option requires the use of GHC 9 or later.

  This feature is experimental.

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

List of closed issues
---------------------

For 2.6.2.1, the following issues were
[closed](https://github.com/agda/agda/issues?q=is%3Aissue+milestone%3A2.6.2.1+is%3Aclosed)
(see [bug tracker](https://github.com/agda/agda/issues)):

  - [#4878](https://github.com/agda/agda/issues/4878): Replace biginteger.js with native BigInt
  - [#5283](https://github.com/agda/agda/issues/5283): Tactic command runs forever
  - [#5291](https://github.com/agda/agda/issues/5291): `match` doesn't work for non-prefix-free cases
  - [#5302](https://github.com/agda/agda/issues/5302): building tests with cabal
  - [#5396](https://github.com/agda/agda/issues/5396): Internal error for rewriting without --confluence-check
  - [#5398](https://github.com/agda/agda/issues/5398): Problem with LaTeX code for multi-line comments with blank lines
  - [#5420](https://github.com/agda/agda/issues/5420): The JS backend generates incorrect code for Agda code that uses reflection
  - [#5421](https://github.com/agda/agda/issues/5421): The GHC backend generates incorrect code for Agda code that uses reflection
  - [#5431](https://github.com/agda/agda/issues/5431): --ghc-strict-data and --ghc-strict
  - [#5433](https://github.com/agda/agda/issues/5433): The JS backend "installs" highlight-hover.js
  - [#5440](https://github.com/agda/agda/issues/5440): (Re)Documenting `catchfilebetweentags` method of building latex files with Agda
  - [#5442](https://github.com/agda/agda/issues/5442): Support GHC 9.2
  - [#5463](https://github.com/agda/agda/issues/5463): Hole in the middle of a record is malformed
  - [#5465](https://github.com/agda/agda/issues/5465): Compilation of Parser.y depends on the locale on Debian too
  - [#5469](https://github.com/agda/agda/issues/5469): `onlyReduceDefs` should not prevent evaluation of macros
  - [#5470](https://github.com/agda/agda/issues/5470): Internal error when using `REWRITE` in `private` block
  - [#5471](https://github.com/agda/agda/issues/5471): LaTeX backend: italics correction
  - [#5473](https://github.com/agda/agda/issues/5473): agda.sty has no version
  - [#5478](https://github.com/agda/agda/issues/5478): Open goal inside record causes internal error (eta-contraction)
  - [#5481](https://github.com/agda/agda/issues/5481): Pattern-matching on records in Prop allows eliminating into Set
  - [#5489](https://github.com/agda/agda/issues/5489): C-c C-x C-a (abort) does not communicate well
  - [#5490](https://github.com/agda/agda/issues/5490): Why does abort (C-c C-x C-a) remove highlighting from the buffer?
  - [#5506](https://github.com/agda/agda/issues/5506): Agda panic: Pattern match failure
  - [#5508](https://github.com/agda/agda/issues/5508): Internal error typechecking non-terminating function on case-insensitive filesystem
  - [#5514](https://github.com/agda/agda/issues/5514): Support GHC 8.10.6
  - [#5531](https://github.com/agda/agda/issues/5531): Internal bug: TypeChecking/Sort
  - [#5532](https://github.com/agda/agda/issues/5532): "The module was successfully compiled" should mention with which backend
  - [#5539](https://github.com/agda/agda/issues/5539): Support GHC 8.10.7
  - [#5544](https://github.com/agda/agda/issues/5544): Internal error caused by addition of `Checkpoints` to `OpenThing`
  - [#5557](https://github.com/agda/agda/issues/5557): Allow Agda to output data files
  - [#5565](https://github.com/agda/agda/issues/5565): Internal error in Agda.TypeChecking.MetaVars
  - [#5593](https://github.com/agda/agda/issues/5593): Compilation failure with `aeson-2`
  - [#5602](https://github.com/agda/agda/issues/5602): The JS backend does not reduce constructor type signatures
  - [#5610](https://github.com/agda/agda/issues/5610): Panic when checking pragma BUILTIN SHARP
  - [#5620](https://github.com/agda/agda/issues/5620): Seemingly incorrect warning for abstract definition without type signature
  - [#5633](https://github.com/agda/agda/issues/5633): Case splitting inserts one with pattern too much (regression in 2.6.2)
  - [#5657](https://github.com/agda/agda/issues/5657): Internal error with postfix projection

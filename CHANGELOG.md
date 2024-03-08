Release notes for Agda version 2.6.5
====================================

Highlights
----------

Installation
------------

* Agda supports GHC versions 8.6.5 to 9.8.1.

Pragmas and options
-------------------

* The following options are now considered infective:
  ([Issue #5264](https://github.com/agda/agda/issues/5264))

  * `--allow-exec`
  * `--cumulativity`
  * `--experimental-irrelevance`
  * `--injective-type-constructors`
  * `--omega-in-omega`
  * `--rewriting`
  * `--type-in-type`

  This means that if a module has one of these flags enabled,
  then all modules importing it must also have that flag enabled.

* New warning `UselessMacro` when a `macro` block does not contain any function definitions.

Syntax
------

Additions to the Agda syntax.

* Left-hand side let: `using x ← e`
  ([PR #7078](https://github.com/agda/agda/pull/7078))

  This new construct can be use in left-hand sides together with `with` and
  `rewrite` to give names to subexpressions. It is the left-hand side
  counterpart of a `let`-binding and supports the same limited form of pattern
  matching on eta-expandable record values.

  It can be quite useful when you have a function doing a series of nested
  `with`s that share some expressions. Something like

  ```agda
  fun : A → B
  fun x using z ← e with foo z
  ... | p with bar z
  ...   | q = r
  ```

  Here the expression `e` doesn't have to be repeated in the two `with`-expressions.

  As in a `with`, multiple bindings can be separated by a `|`, and variables to
  the left are in scope in bindings to the right.

Language
--------

Changes to type checker and other components defining the Agda language.

Reflection
----------

Changes to the meta-programming facilities.

Library management
------------------

Interaction and emacs mode
--------------------------

* The Auto command has been reimplemented from the ground up
  ([PR #6410](https://github.com/agda/agda/pull/6410)).
  This fixes problems where Auto would fail in the presence of language features
  it did not know about, such as copatterns or anything cubical.

  The reimplementation does not support case splitting (`-c`), disproving
  (`-d`) or refining (`-r`).

Backends
--------

API
---

Highlighting some changes to Agda as a library.

* New module `Agda.Syntax.Common.KeywordRange` providing type `KwRange` isomorphic to `Range`
  to indicate source positions that just span keywords ([PR #7162](https://github.com/agda/agda/pull/7162)).
  The motivation for `KwRange` is to distinguish such ranges from ranges for whole subtrees,
  e.g. in data type `Agda.Syntax.Concrete.Declaration`.

  API:
  ```haskell
  module Agda.Syntax.Common.KeywordRange where

  type KwRange

  -- From Range to KwRange
  kwRange :: HasRange a => a -> KwRange

  -- From KwRange to Range
  instance HasRange KwRange where
    getRange :: KwRange -> Range
  ```

Other issues closed
-------------------

For 2.6.5, the following issues were also
[closed](https://github.com/agda/agda/issues?q=is%3Aissue+milestone%3A2.6.5+is%3Aclosed)
(see [bug tracker](https://github.com/agda/agda/issues)):

NOTE: This section will be filled by output produced with `closed-issues-for-milestone 2.6.5`.

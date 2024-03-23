Release notes for Agda version 2.6.5
====================================

Highlights
----------

Installation
------------

* Agda supports GHC versions 8.6.5 to 9.8.2.

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

* New warning `ConflictingPragmaOptions` if giving both `--this` and `--that`
  when `--this` implies `--no-that` (and analogous for `--no-this` implies
  `--that`, etc).

* [**Breaking**] The option `--overlapping-instances`, which allows
  backtracking during instance search, has been renamed to
  `--backtracking-instance-search`.

* New warning `WarningProblem` when trying to switch an unknown or non-benign warning with the `-W` option.
  Used to be a hard error.

* New option `--require-unique-meta-solutions` (turned on by default). Disabling it with
  `--no-require-unique-meta-solutions` allows the type checker to take advantage of `INJECTIVE_FOR_INFERENCE` pragmas
  (see below). The `--lossy-unification` flag implies `--no-require-unique-meta-solutions`.

* New pragma `INJECTIVE_FOR_INFERENCE`, which treats functions as injective for inferring implicit arguments if
  `--no-require-unique-meta-solutions` is given. The `--no-require-unique-meta-solutions` flag needs to be given in the
  file where the function is used, and not necessarily in the file where it is defined.
  For example:
  ```agda
  reverse-≡ : {l l' : List A} → reverse l ≡ reverse l' → reverse l ≡ reverse l'
  reverse-≡ h = h

  []≡[] : {l l' : List A} → [] ≡ []
  []≡[] = reverse-≡ (refl {x = reverse []})
  ```
  does not work since Agda won't solve `l` and `l'` for `[]`, even though it knows `reverse l = reverse []`. If `reverse` is
  marked as injective with `{-# INJECTIVE_FOR_INFERENCE reverse #-}` this example will work.

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

* Type-based termination checker

  Agda is now able to understand polymorphic functions during checking for structural recursion.
  Some non-polymoprhic functions may also be recognized as size preserving, which leads to acceptance of the following functions:

   ```agda
  div : Nat → Nat → Nat
  div zero    y = zero 
  div (suc x) y = suc (div (minus x y) y)

  qsort : {A : Set} → (A → A → Bool) → List A → List A
  qsort _ nil = nil
  qsort cmp (cons x xs) = qsort cmp (filter (cmp x) xs) ++ cons x (qsort cmp (filter (λ y → cmp y x) xs))
  ```

  Type-based termination checking also works for coinduction, which improves the guardedness predicate.

  See [user manual](https://agda.readthedocs.io/en/v2.7.0/tools/type-based-termination-checking.html)
  for more.

* Pattern synonyms can now expose existing instance arguments
  ([PR 7173](https://github.com/agda/agda/pull/7173)).
  Example:
  ```agda
  data D : Set where
    c : {{D}} → D

  pattern p {{d}} = c {{d}}
  ```
  This allows us to explicitly bind these argument in a pattern match
  and supply them explicitly when using the pattern synonym in an expression.
  ```agda
  f : D → D
  f (p {{d = x}}) = p {{d = x}}
  ```

  We cannot create new instance arguments this way, though.
  The following is rejected:
  ```agda
  data D : Set where
    c : D → D

  pattern p {{d}} = c d
  ```


Language
--------

Changes to type checker and other components defining the Agda language.

* Agda now uses *discrimination trees* to store and look up instance
  definitions, rather than linearly searching through all instances for
  a given "class" ([PR #7109](https://github.com/agda/agda/pull/7109)).

  This is a purely internal change, and should not result in any change
  to which programs are accepted or rejected. However, it significantly
  improves the performance of instance search, especially for the case
  of a "type class" indexed by a single type argument. The new lookup
  procedure should never be slower than the previous implementation.

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

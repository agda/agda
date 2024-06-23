Release notes for Agda version 2.6.5
====================================

Highlights
----------

Installation
------------

* Agda supports GHC versions 8.6.5 to 9.10.1.

Pragmas and options
-------------------

* These options are now on by default:

  * `--exact-split`: Warn about clauses that are not definitional equalities.
  * `--keep-pattern-variables`: Do not introduce dot patterns in interactive splitting.
  * `--postfix-projections`: Print projections and projection patterns in postfix.
  * `--save-metas`: Try to not unfold metavariable solutions in interface files.

  To revert to the old behavior, use options `--no-...`.

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

* New warning `CoinductiveEtaRecord` if a record is declared both `coinductive` and having `eta-equality`.
  Used to be a hard error; now Agda continues, ignoring `eta-equality`.

* New warning `DuplicateRecordDirectives` if e.g. a `record` is declared both `inductive` and `coinductive`,
  or declared `inductive` twice.

* New warning `ConflictingPragmaOptions` if giving both `--this` and `--that`
  when `--this` implies `--no-that` (and analogous for `--no-this` implies
  `--that`, etc).

* New error warning `ConstructorDoesNotFitInData` when a constructor parameter
  is too big (in the sense of universe level) for the target data type of the constructor.
  Used to be a hard error.

* Rejected rewrite rules no longer cause a hard error but instead cause
  an error warning. The following warnings were added to document the
  various reasons for rejection:
  * `RewriteLHSNotDefinitionOrConstructor`
  * `RewriteVariablesNotBoundByLHS`
  * `RewriteVariablesBoundMoreThanOnce`
  * `RewriteLHSReduces`
  * `RewriteHeadSymbolIsProjection`
  * `RewriteHeadSymbolIsProjectionLikeFunction`
  * `RewriteHeadSymbolIsTypeConstructor`
  * `RewriteHeadSymbolContainsMetas`
  * `RewriteConstructorParametersNotGeneral`
  * `RewriteContainsUnsolvedMetaVariables`
  * `RewriteBlockedOnProblems`
  * `RewriteRequiresDefinitions`
  * `RewriteDoesNotTargetRewriteRelation`
  * `RewriteBeforeFunctionDefinition`
  * `RewriteBeforeMutualFunctionDefinition`

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
  postulate
    reverse-≡ : {l l' : List A} → reverse l ≡ reverse l' → reverse l ≡ reverse l'

  []≡[] : [] ≡ []
  []≡[] = reverse-≡ (refl {x = reverse []})
  ```
  does not work since Agda won't solve `l` and `l'` for `[]`, even though it knows `reverse l = reverse []`.
  If `reverse` is marked as injective with `{-# INJECTIVE_FOR_INFERENCE reverse #-}` this example will work.

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

* Add new primitive to run instance search from reflection code:

  ```agda
    -- Try to solve open instance constraints. When wrapped in `noConstraints`,
    -- fails if there are unsolved instance constraints left over that originate
    -- from the current macro invokation. Outside constraints are still attempted,
    -- but failure to solve them are ignored by `noConstraints`.
    solveInstanceConstraints : TC ⊤
  ```

* A new reflection primitive `workOnTypes : TC A → TC A` was added to
  `Agda.Builtin.Reflection`. This runs the given computation at the type level,
  which enables the use of erased things. In particular, this is needed when
  working with (dependent) function types with erased arguments. For example,
  one can get the type of the tuple constructor `_,_` (which now takes its type
  parameters as erased arguments, see above) and unify it with the current goal
  as follows:
  ```agda
  macro
    testM : Term → TC ⊤
    testM hole = bindTC (getType (quote _,_)) (λ t → workOnTypes (unify hole t))

  typeOfComma = testM
  ```

* Erased constructors are now supported in reflection machinery.
  Quantity argument was added to `data-cons`. For erased constructors this
  argument has a value of `quantity-0`, otherwise it's `quantity-ω`.
  `defineData` now requires setting quantity for each constructor.

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

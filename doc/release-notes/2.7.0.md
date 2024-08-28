Release notes for Agda version 2.7.0
====================================

Highlights
----------

* Mimer, a re-implementation of the "auto" term synthesizer, replaces Agsy.

* New syntax `using x ← e` to bind values on the left-hand-side of a function clause.

* Instance search is more performant thanks to a new indexing structure.
  Additionally, users can now control how instances should be selected
  in the case multiple candidates exist.

* User-facing options ~~`--exact-split`,~~ `--keep-pattern-variables`, and `--postfix-projections`
  are now on by default.

Installation
------------

* Agda versioning scheme switches to the [Haskell Package Versioning Policy](https://pvp.haskell.org/)
  so Agda can be more reliably used as a library.
  Major releases will now bump the second number in the version tuple: 2.7.0, 2.8.0, 2.9.0, ...

* When the creation of the Agda library interface files fails during installation,
  a warning is emitted rather than aborting installation.
  The absence of these interface files is not a problem if the Agda installation
  resides in user space; they will be created on the fly then.
  Yet for system-wide installations in root space or packaging,
  the interface files should be created.
  This can be achieved by a manual invocation of Agda on the library source files
  (i.e., primitive and builtin modules `Agda.*`).
  (See [Issue #7401](https://github.com/agda/agda/issues/7401) and [PR #7404](https://github.com/agda/agda/pull/7404).)

* Agda supports GHC versions 8.6.5 to 9.10.1.

Pragmas and options
-------------------

* [**Breaking**] The option `--overlapping-instances`, which allows
  backtracking during instance search, has been renamed to
  `--backtracking-instance-search`.

* These options are now on by default:

  * ~~`--exact-split`: Warn about clauses that are not definitional equalities.~~
  * `--keep-pattern-variables`: Do not introduce dot patterns in interactive splitting.
  * `--postfix-projections`: Print projections and projection patterns in postfix.
  * `--save-metas`: Try to not unfold metavariable solutions in interface files.

  To revert to the old behavior, use options `--no-...`.

* Option `--rewriting` is now considered infective.
  This means that if a module has this flag enabled,
  then all modules importing it must also have that flag enabled.

* New warnings:

  * `CoinductiveEtaRecord` if a record is declared both `coinductive` and having `eta-equality`.
    Used to be a hard error; now Agda continues, ignoring `eta-equality`.

  * `ConflictingPragmaOptions` if giving both `--this` and `--that`
    when `--this` implies `--no-that` (and analogous for `--no-this` implies
    `--that`, etc).

  * `ConstructorDoesNotFitInData` when a constructor parameter
    is too big (in the sense of universe level) for the target data type of the constructor.
    Error warning, used to be a hard error.

  * `DuplicateRecordDirectives` if e.g. a `record` is declared both `inductive` and `coinductive`,
    or declared `inductive` twice.

  * `UselessMacro` when a `macro` block does not contain any function definitions.

  * `WarningProblem` when trying to switch an unknown or non-benign warning with the `-W` option.
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

### Lossy unification

* [New option `--require-unique-meta-solutions`](https://agda.readthedocs.io/en/v2.7.0/tools/command-line-options.html#cmdoption-require-unique-meta-solutions)
  (turned on by default).
  Disabling it with `--no-require-unique-meta-solutions` allows the type checker
  to take advantage of `INJECTIVE_FOR_INFERENCE` pragmas (see below).
  The `--lossy-unification` flag implies `--no-require-unique-meta-solutions`.

* [New pragma `INJECTIVE_FOR_INFERENCE`](https://agda.readthedocs.io/en/v2.7.0/pragmas.html#injective-for-inference-pragma)
  which treats functions as injective for inferring implicit arguments if
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

* [Left-hand side let](https://agda.readthedocs.io/en/v2.7.0/with-abstraction.html#left-hand-side-let-bindings):
  `using x ← e`
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

* [**Breaking**] Erased constructors are now supported in reflection machinery.
  Quantity argument was added to `data-cons`. For erased constructors this
  argument has a value of `quantity-0`, otherwise it's `quantity-ω`.
  `defineData` now requires setting quantity for each constructor.

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

Interaction and emacs mode
--------------------------

* [**Breaking**] [The Auto command](https://agda.readthedocs.io/en/v2.7.0/tools/auto.html)
  _Agsy_ has been replaced by an entirely new implementation _Mimer_
  ([PR #6410](https://github.com/agda/agda/pull/6410)).
  This fixes problems where Auto would fail in the presence of language features
  it did not know about, such as copatterns or anything cubical.

  The reimplementation does not support case splitting (`-c`), disproving
  (`-d`) or refining (`-r`).

* The Agda input method for Emacs has been extended by several character bindings.
  The list of changes can be obtained with a git diff on the sources:
  ```
  git diff v2.6.4.3 v2.7.0 -- src/data/emacs-mode/agda-input.el
  ```

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

* New hook in ``Agda.Compiler.ToTreeless`` to enable custom pipelines in compiler backends
  ([PR #7273](https://github.com/agda/agda/pull/7273)).


List of closed issues
---------------------

For 2.7.0, the following issues were
[closed](https://github.com/agda/agda/issues?q=is%3Aissue+milestone%3A2.7.0+is%3Aclosed)
(see [bug tracker](https://github.com/agda/agda/issues)):

- [Issue #2492](https://github.com/agda/agda/issues/2492): Limit the size of terms agsy is allowed to insert
- [Issue #2853](https://github.com/agda/agda/issues/2853): Auto does not work well with record types
- [Issue #4594](https://github.com/agda/agda/issues/4594): Improve the blocking primitive
- [Issue #4777](https://github.com/agda/agda/issues/4777): Interaction between tactics and instance search
- [Issue #5264](https://github.com/agda/agda/issues/5264): Should more flags be infective (or have coinfective negations)?
- [Issue #6101](https://github.com/agda/agda/issues/6101): Agsy gives up when no HIT is present
- [Issue #6124](https://github.com/agda/agda/issues/6124): Reflection: cannot reduce type because variable is erased
- [Issue #6181](https://github.com/agda/agda/issues/6181): Agda incorrectly reports type error when an identity function is not properly hidden from the termination checker
- [Issue #6270](https://github.com/agda/agda/issues/6270): Irrelevance in the type of a record module definition
- [Issue #6292](https://github.com/agda/agda/issues/6292): Document interaction between reflection and erasure
- [Issue #6335](https://github.com/agda/agda/issues/6335): Error message for non-canonical value when using Show instances is confusing
- [Issue #6361](https://github.com/agda/agda/issues/6361): Agsy ignores --postfix-projections
- [Issue #6406](https://github.com/agda/agda/issues/6406): Subject reduction problem related to projections with non-erased parameter arguments
- [Issue #6433](https://github.com/agda/agda/issues/6433): Add unicode character BALLOT X as \crossmark to Agda input mode
- [Issue #6509](https://github.com/agda/agda/issues/6509): Agda seems to be very slow at typechecking records with many fields
- [Issue #6584](https://github.com/agda/agda/issues/6584): Case splitting on record renames top-level function
- [Issue #6643](https://github.com/agda/agda/issues/6643): Rewrite rules are allowed in implicit mutual blocks
- [Issue #6663](https://github.com/agda/agda/issues/6663): Function arguments are nonvariant more often than they should be
- [Issue #6667](https://github.com/agda/agda/issues/6667): An internal error occurrs when (mis)using syntax declarations
- [Issue #6744](https://github.com/agda/agda/issues/6744): Alias in constructor index foils the forcing analysis
- [Issue #6768](https://github.com/agda/agda/issues/6768): auto: not implemented HITs error on non-cubical code
- [Issue #6783](https://github.com/agda/agda/issues/6783): `@tactic` does not kick in for lambdas
- [Issue #6806](https://github.com/agda/agda/issues/6806): Remove `GenericWarning`
- [Issue #6841](https://github.com/agda/agda/issues/6841): Uncaught pattern violation when using `with...in...` instead of old-school inspect
- [Issue #6866](https://github.com/agda/agda/issues/6866): User Manual: Make Installation as Easy as Possible
- [Issue #6867](https://github.com/agda/agda/issues/6867): Agda rejects identity function on indexed datatype with erased index
- [Issue #6919](https://github.com/agda/agda/issues/6919): improving formatting of warnings/errors
- [Issue #6943](https://github.com/agda/agda/issues/6943): Making `--exact-split` and `--postfix-projections` default?
- [Issue #6945](https://github.com/agda/agda/issues/6945): Missing warning for non-empty but effectless `private` blocks
- [Issue #6976](https://github.com/agda/agda/issues/6976): Unexpected failure of instance resolution
- [Issue #7017](https://github.com/agda/agda/issues/7017): Document instance projections
- [Issue #7058](https://github.com/agda/agda/issues/7058): Unclear specification and correctness of TypeChecking/DeadCode
- [Issue #7090](https://github.com/agda/agda/issues/7090): REWRITE rule with confluence, inconsistencies with documentation and error messages
- [Issue #7123](https://github.com/agda/agda/issues/7123): Citation.cff
- [Issue #7136](https://github.com/agda/agda/issues/7136): Pattern synonyms with named arguments can be defined but not used
- [Issue #7146](https://github.com/agda/agda/issues/7146): Misprinted domain-free parameters with cohesion attribute
- [Issue #7158](https://github.com/agda/agda/issues/7158): Non-sensical error since 2.5.4 when applying a non-function
- [Issue #7167](https://github.com/agda/agda/issues/7167): Underapplied pattern synonyms expand to lambdas with wrong hiding in expressions
- [Issue #7170](https://github.com/agda/agda/issues/7170): Confusing error "Unused variable in pattern synonym"
- [Issue #7176](https://github.com/agda/agda/issues/7176): Instanceness is lost when expanding absurd pattern in pattern synonym expression
- [Issue #7177](https://github.com/agda/agda/issues/7177): No scope info for underscores inserted by pattern synonym expansion
- [Issue #7181](https://github.com/agda/agda/issues/7181): Forcing translation prevents reduction within function definition
- [Issue #7182](https://github.com/agda/agda/issues/7182): `getDefinition` gives wrong constructor for record from applied parameterised module
- [Issue #7187](https://github.com/agda/agda/issues/7187): Sort metas produce ill-typed reflected terms when quoted
- [Issue #7191](https://github.com/agda/agda/issues/7191): `show` does not respect `abstract`/`opaque` when normalising a term in a hole
- [Issue #7192](https://github.com/agda/agda/issues/7192): GHC 9.10
- [Issue #7193](https://github.com/agda/agda/issues/7193): Agda always has irrelevant projections
- [Issue #7196](https://github.com/agda/agda/issues/7196): Regression when giving instances with visible arguments
- [Issue #7202](https://github.com/agda/agda/issues/7202): `ModuleDoesntExport` has imprecise deadcode highlighting
- [Issue #7208](https://github.com/agda/agda/issues/7208): Importing module with wrong namespace causes internal error instead of user-friendly error.
- [Issue #7218](https://github.com/agda/agda/issues/7218): Internal error in opaque block when case splitting when just given extended lambda
- [Issue #7219](https://github.com/agda/agda/issues/7219): Only warn about unknown warnings, don't fail hard
- [Issue #7227](https://github.com/agda/agda/issues/7227): Save-metas causes OOM during macro execution
- [Issue #7236](https://github.com/agda/agda/issues/7236): Expected a hidden argument, but found a visible argument in with-abstraction when using REWRITE
- [Issue #7262](https://github.com/agda/agda/issues/7262): Error "This clause has target type ... which is not usable" highlights pattern instead of clause
- [Issue #7266](https://github.com/agda/agda/issues/7266): Internal error at Agda/TypeChecking/Substitute.hs:140:33
- [Issue #7286](https://github.com/agda/agda/issues/7286): Hard error on `instance` definition with unsolved type
- [Issue #7301](https://github.com/agda/agda/issues/7301): Agda >=2.6.3 hangs on conflicting record directives
- [Issue #7318](https://github.com/agda/agda/issues/7318): `--postfix-projections` do not make use of mixfix syntax
- [Issue #7326](https://github.com/agda/agda/issues/7326): Internal error on pattern lambda with no clauses
- [Issue #7329](https://github.com/agda/agda/issues/7329): wrong type for unnamed record constructor
- [Issue #7331](https://github.com/agda/agda/issues/7331): Search for project root crashes when (parent) directory lacks permissions
- [Issue #7332](https://github.com/agda/agda/issues/7332): quoteTerm loops on dependent copattern lambda
- [Issue #7337](https://github.com/agda/agda/issues/7337): Caching loses reflection-generated pragmas
- [Issue #7346](https://github.com/agda/agda/issues/7346): Proof of ⊥ using HIT-indexed type

These (relevant) pull requests were merged for 2.7.0:

- [PR #5267](https://github.com/agda/agda/issues/5267): Make more flags infective
- [PR #6410](https://github.com/agda/agda/issues/6410): Mimer: a drop-in replacement for Agsy
- [PR #6569](https://github.com/agda/agda/issues/6569): Do final checks before freezing metas
- [PR #6570](https://github.com/agda/agda/issues/6570): Coerce `unquote` applications
- [PR #6640](https://github.com/agda/agda/issues/6640): Add `INJECTIVE_FOR_INFERENCE` pragma
- [PR #6674](https://github.com/agda/agda/issues/6674): Testcase for fixed #6542
- [PR #6769](https://github.com/agda/agda/issues/6769): Various symbol additions to agda-input
- [PR #6870](https://github.com/agda/agda/issues/6870): [ fix #6867 ] Only consider arguments with @0 for forcing if --erasure is on
- [PR #6978](https://github.com/agda/agda/issues/6978): [ fix #6976 ] Add constraint for resolving the head of an instance
- [PR #7055](https://github.com/agda/agda/issues/7055): Unspine system projections when they have display forms
- [PR #7071](https://github.com/agda/agda/issues/7071): Eta-expand mismatched cubical primitives
- [PR #7078](https://github.com/agda/agda/issues/7078): Left-hand side `let`
- [PR #7103](https://github.com/agda/agda/issues/7103): [ re #5267 ] Add new infective options to user manual
- [PR #7109](https://github.com/agda/agda/issues/7109): Discrimination trees for instance search
- [PR #7115](https://github.com/agda/agda/issues/7115): Flake improvements
- [PR #7119](https://github.com/agda/agda/issues/7119): Split GenericWarning into individual warnings
- [PR #7121](https://github.com/agda/agda/issues/7121): Update installation.rst
- [PR #7138](https://github.com/agda/agda/issues/7138): Fix #7136: proper error when pattern definition has unsupported arguments
- [PR #7142](https://github.com/agda/agda/issues/7142): Fix #6783: error for @tactic on lambda
- [PR #7144](https://github.com/agda/agda/issues/7144): Add reference to Cornelis in the documentation
- [PR #7147](https://github.com/agda/agda/issues/7147): Fix #7146: printing of cohesion and lock attributes
- [PR #7149](https://github.com/agda/agda/issues/7149): Fix mutual information not being set properly by the positivity checker
- [PR #7155](https://github.com/agda/agda/issues/7155): Fix #6866: User Manual: Make Installation as Easy as Possible
- [PR #7159](https://github.com/agda/agda/issues/7159): Fix #7158: Application: check for sufficient arity before checking target
- [PR #7160](https://github.com/agda/agda/issues/7160): Fix #6667: case not `__IMPOSSIBLE__` for nullary syntax
- [PR #7161](https://github.com/agda/agda/issues/7161): Fix #6945: warn about useless private even in absense of nice decls
- [PR #7162](https://github.com/agda/agda/issues/7162): Blocks in Concrete syntax: store Range of block keyword
- [PR #7168](https://github.com/agda/agda/issues/7168): Fix #7167: type checking underapplied pattern synonyms
- [PR #7169](https://github.com/agda/agda/issues/7169): Trigger and improve error UnusedVariableInPatternSynonym
- [PR #7173](https://github.com/agda/agda/issues/7173): Part of #2829: Allow instance arguments in pattern synonyms that are such in the pattern already
- [PR #7179](https://github.com/agda/agda/issues/7179): Fix #7177: only setScope when scope is not null
- [PR #7180](https://github.com/agda/agda/issues/7180): Use compareAs for assignE even in compareAtom
- [PR #7183](https://github.com/agda/agda/issues/7183): Instance overlap pragmas
- [PR #7185](https://github.com/agda/agda/issues/7185): Fix #7176: turn absurd pattern in instance position to instance meta
- [PR #7197](https://github.com/agda/agda/issues/7197): Re. #7196: Only prune instances in serialised iface
- [PR #7203](https://github.com/agda/agda/issues/7203): Fix incorrectly quoted sorts
- [PR #7204](https://github.com/agda/agda/issues/7204): Fix #7202: ModuleDoesntExport: only highlight missing names
- [PR #7209](https://github.com/agda/agda/issues/7209): Fix #7208: restore missing check for OverlappingProjects
- [PR #7210](https://github.com/agda/agda/issues/7210): Fix range for deprecated module import warning when applied
- [PR #7211](https://github.com/agda/agda/issues/7211): Fix #7181: Allow matching to continue when stuck on lazy pattern
- [PR #7222](https://github.com/agda/agda/issues/7222): Fix #7219: only warn about problems with warning options
- [PR #7231](https://github.com/agda/agda/issues/7231): Instantiate terms before traversing them in tcExtendContext
- [PR #7237](https://github.com/agda/agda/issues/7237): Fix #7236: use context rather than telescope for lambda-bound variables in rewrite patterns
- [PR #7238](https://github.com/agda/agda/issues/7238): Build with GHC 9.10
- [PR #7241](https://github.com/agda/agda/issues/7241): Drop time-compat dependency and Stack LTS for GHC 8.6
- [PR #7243](https://github.com/agda/agda/issues/7243): re. 7218: Saturate opaque blocks after Give commands
- [PR #7248](https://github.com/agda/agda/issues/7248): Overhaul dead code elimination, make --save-metas the default
- [PR #7249](https://github.com/agda/agda/issues/7249): docs/installation: point new wiki
- [PR #7251](https://github.com/agda/agda/issues/7251): re. 7250: copy instanceinfo
- [PR #7252](https://github.com/agda/agda/issues/7252): Fix #7193: persistently remember what is a projection
- [PR #7260](https://github.com/agda/agda/issues/7260): Reflection primitive to solve instances
- [PR #7273](https://github.com/agda/agda/issues/7273): ToTreeless: allow backends to define custom pipelines
- [PR #7274](https://github.com/agda/agda/issues/7274): #7182: copied records should refer to the copied constructor and fields
- [PR #7276](https://github.com/agda/agda/issues/7276): #7191: respect abstract mode when using show function
- [PR #7283](https://github.com/agda/agda/issues/7283): agdaLatex  documentation
- [PR #7292](https://github.com/agda/agda/issues/7292): New error warning `ConstructorDoesNotFitInData` instead of hard error.
- [PR #7298](https://github.com/agda/agda/issues/7298): Remove fiddly attempt at instance postponement
- [PR #7300](https://github.com/agda/agda/issues/7300): New deadcode warning CoinductiveEtaRecord instead of GenericError
- [PR #7302](https://github.com/agda/agda/issues/7302): Fix #7301 (loop in parser): move verifyRecordDirectives to scope checker
- [PR #7305](https://github.com/agda/agda/issues/7305): Fix #7286: don't fail hard when there are instances with unresolved types
- [PR #7307](https://github.com/agda/agda/issues/7307): fix #7017: document instance projections
- [PR #7310](https://github.com/agda/agda/issues/7310): Add `workOnTypes` reflection primitive
- [PR #7311](https://github.com/agda/agda/issues/7311): [ #6406 ] Add test cases from discussion on this issue
- [PR #7313](https://github.com/agda/agda/issues/7313): Update universe-levels.lagda.rst
- [PR #7314](https://github.com/agda/agda/issues/7314): Add constructors for custom backend warning/errors
- [PR #7315](https://github.com/agda/agda/issues/7315): same shadowing logic for record patterns as for constructor patterns in absToCon
- [PR #7316](https://github.com/agda/agda/issues/7316): add \crossmark to emacs input mode
- [PR #7317](https://github.com/agda/agda/issues/7317): Don't mark eta unit records as irrelevant
- [PR #7319](https://github.com/agda/agda/issues/7319): Make --postfix-projections the default
- [PR #7320](https://github.com/agda/agda/issues/7320): Turn on --exact-split by default
- [PR #7322](https://github.com/agda/agda/issues/7322): Expose constructor erasure in reflection interface
- [PR #7325](https://github.com/agda/agda/issues/7325): add CSS rule for macro names
- [PR #7327](https://github.com/agda/agda/issues/7327): proper error instead of impossible for clauseless pat-lam
- [PR #7330](https://github.com/agda/agda/issues/7330): [#7329] Correct module name in module applications
- [PR #7333](https://github.com/agda/agda/issues/7333): [#7332] don't loop when quoting dependent copattern lambdas
- [PR #7334](https://github.com/agda/agda/issues/7334): Fix #7331: handle permission error in search for project file
- [PR #7336](https://github.com/agda/agda/issues/7336): Remove duplicate imports and pragmas in MAlonzo
- [PR #7338](https://github.com/agda/agda/issues/7338): (#7337) foreign code needs to go in post-scope state
- [PR #7343](https://github.com/agda/agda/issues/7343): Turn illegal rewrite rules into an error warning
- [PR #7347](https://github.com/agda/agda/issues/7347): [ fix #7266 ] Check that constructor names match before projecting in `matchPattern`
- [PR #7349](https://github.com/agda/agda/issues/7349): Fix #7346 by not considering HIT-constructor arguments forced
- [PR #7350](https://github.com/agda/agda/issues/7350): Fix #6744 by reducing during forcing analysis.
- [PR #7352](https://github.com/agda/agda/issues/7352): Fix issue 7262: Range of the lhs modality check
- [PR #7353](https://github.com/agda/agda/issues/7353): Update installation docs (e.g. re #7163: document installation problems with `executable-dynamic`)
- [PR #7355](https://github.com/agda/agda/issues/7355): Make `--keep-pattern-variables` the default
- [PR #7356](https://github.com/agda/agda/issues/7356): Add --save-metas default to CHANGELOG
- [PR #7358](https://github.com/agda/agda/issues/7358): [ doc ] Document `--termination-depth` in user manual
- [PR #7359](https://github.com/agda/agda/issues/7359): Fix #7354 by making types of live metas live in DeadCode
- [PR #7360](https://github.com/agda/agda/issues/7360): Fix for issue #6841 and related changes
- [PR #7362](https://github.com/agda/agda/issues/7362): Fix #6919: separate warnings by empty line
- [PR #7364](https://github.com/agda/agda/issues/7364): Resolve instance overlap for irrelevant metas
- [PR #7367](https://github.com/agda/agda/issues/7367): Minor fixes to instance overlap + constraint postponement

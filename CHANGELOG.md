Release notes for Agda version 2.9.0
====================================

Highlights
----------

* Option `-j` to type check modules in parallel in batch mode (experimental; Amélia Liao).
* Substantial performance improvements (András Kovács, Amélia Liao Reed Mullanix).
* Agda on WASM (Jonathan Coates, Andy Pan).
* Qualified `do` (Amélia Liao).
* Local rewrite rules (experimental; Nathaniel Burke, Jesper Cockx).
* Improved termination checker for copatterns (Nate Soares).
* Warning about unused imports (experimental; Andreas Abel).
* Emacs: Syntax highlighting in the Agda information buffer (Andreas Abel, Amélia Liao).
* Improvements to automatic term synthesis, "Mimer" (Andreas Abel, Jesper Cockx).
* Forester backend (Lîm Tsú-thuàn).
* Around 60 fixes of inconsistencies, internal errors, and regressions.
* Around 130 other issues fixed.

Installation
------------

* Dropped support for GHC 8.8, 8.10, and 9.0.

* Agda supports GHC versions 9.2.8 to 9.14.1.

* The new Cabal flag `version-with-git-hash` controls whether version information
  is suffixed with the Git commit hash. It is disabled by default for cabal
  but enabled by default when using the Makefile.

Pragmas and options
-------------------

* New option `--parallel` (`-j` for short, as in `make`) lets Agda
  type-check imported modules in parallel. For large libraries, this can
  result in a speedup of ~3x, at the cost of roughly doubling the
  maximum memory usage.
  This option does not yet work well with `--interaction`
  ([issue #8477](https://github.com/agda/agda/issues/8477)).

* New option `--print-options` to print a simple list of all options.
  This list can e.g. be used to implement bash completion.

* The flavor of Cubical Agda can now be chosen by an argument to the `--cubical` option:

  | Old                    | New                                               |
  | ---------------------- | ------------------------------------------------- |
  | `--cubical`            | `--cubical`, or `--cubical=full`                  |
  | `--erased-cubical`     | `--erased-cubical`, or `--cubical=erased`         |
  | `--cubical-compatible` | `--cubical-compatible`, or `--cubical=compatible` |
  | -                      | `--cubical=no-glue`                               |

  For compatibility between modules using different variants of Cubical Agda, see
  [the documentation](https://agda.readthedocs.io/en/v2.9.0/language/cubical.html#variants).

* New flag `--no-write-interfaces`.

* New command-line option `--literate-markdown-only-agda-blocks` (off by default).
  When enabled, only code blocks explicitly marked with ` ```agda ` are treated as
  Agda code in literate Markdown (`.lagda.md`) and Typst (`.lagda.typ`) files.
  Unmarked code blocks (` ``` `) are treated as verbatim text and not type-checked.
  This option must be set via command line since it affects parsing.
  (See [#7971](https://github.com/agda/agda/issues/7971).)

* The flag `--termination-depth=N` now means _maximum_ termination depth and
  the termination checker now performs iterative deepening,
  starting with depth `1` and increasing it up to the given `N`, stopping early
  as soon as the termination check succeeds.
  Increasing `N` can thus slow down things only for failing termination checks.

  The default value of `N` has been increased from `1` to `3`, yet not higher,
  because cases requiring a termination depth `> 1` are already very rare in practice.

  There is also an internal change to the termination checker.
  Dot patterns are now taken into account from the beginning and not only when
  the termination check fails without taking them into account.
  The overhead to also mine dot patterns for structural descent was already
  negligible so it made sense to simplify the termination checking algorithm.

* The new flag `--no-occurrence-analysis` can be used to turn off the
  automated occurrence analysis for functions.

  By default Agda analyses how functions use their arguments. For
  instance, Agda can tell that `D` in the following code is strictly
  positive, because `Vec` uses its `Set` argument in a strictly
  positive way:
  ```agda
  open import Agda.Builtin.Nat
  open import Agda.Builtin.Unit

  data _×_ (A B : Set) : Set where
    _,_ : A → B → A × B

  Vec : Set → Nat → Set
  Vec A zero    = ⊤
  Vec A (suc n) = A × Vec A n

  data D : Set where
    c : ∀ n → Vec D n → D
  ```
  However, this analysis can be slow, especially for big mutual
  blocks. Now it is possible to turn it off.

  The analysis is also used to detect unused function arguments. The
  following code is by default accepted, but it is rejected if the
  occurrence analysis is turned off:
  ```agda
  open import Agda.Builtin.Bool
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Unit

  F : Bool → Set → Set
  F true  _ = Bool
  F false _ = ⊤

  _ : {b : Bool} → F b Bool ≡ F b ⊤
  _ = refl
  ```

  Note that an alternative to the analysis is to use polarities. The
  following code is accepted:
  ```agda
  {-# OPTIONS --polarity --no-occurrence-analysis #-}

  open import Agda.Builtin.Bool
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Agda.Builtin.Unit

  data _×_ (@++ A B : Set) : Set where
    _,_ : A → B → A × B

  Vec : @++ Set → Nat → Set
  Vec A zero    = ⊤
  Vec A (suc n) = A × Vec A n

  data D : Set where
    c : ∀ n → Vec D n → D

  F : Bool → @unused Set → Set
  F true  _ = Bool
  F false _ = ⊤

  _ : {b : Bool} → F b Bool ≡ F b ⊤
  _ = refl
  ```

* Setting environment variable `NO_COLOR` now turns off coloring in the default `--color=auto` mode.
  It can be overwritten by `--color=always`.
  See also https://no-color.org/ .

* New option `--quote-metas` to allow for `quoteTerm` constraints to
  be solved even when the quoted term contains unsolved metas.
  This allows for elaborating macro applications with quoted arguments
  that still have interactive holes in them.
  See the [quote metas documentation](https://agda.readthedocs.io/en/v2.9.0/language/reflection.html#quote-metas).

* `{-# NO_POSITIVITY_CHECK #-}` pragmas are now recognized in `record` declarations and `where` blocks,
  and pertain to the following `data` or `record` declaration or mutual block.

* New option `--local-rewriting` which enables parameterising over computation rules by annotating module parameters with `@rewrite` attributes. See the [local rewriting documentation](https://agda.readthedocs.io/en/v2.9.0/language/local-rewriting.html) for more info.

* New `primRewriteNoMatch` primitive in `Agda.Builtin.Equality.Rewrite` for controlling rewrite rule matching. See the section in the [rewriting documentation](https://agda.readthedocs.io/en/v2.9.0/language/rewriting.html#controlling-rewrite-rule-matching-with-primrewritenomatch) for more info.

* The `ETA` pragma has been removed.

* Eta-equality for record types is no longer inferred.
  Previously Agda would switch off eta for a recursive record type automatically
  if there was a risk that the type checker could loop due to infinite eta expansion.
  Now, Agda will only flag it with an `UnguardedEtaRecord` error, so one has to add
  a `no-eta-equality` directive manually.
  If one wants eta enabled nevertheless, one can use the new `ETA_EQUALITY` pragma.
  This pragma replaces the old `ETA` pragma and can also be used to turn on eta for
  `coinductive` record types.
  See the documentation on
  [unguarded records](https://agda.readthedocs.io/en/v2.9.0/language/record-types.html#unguarded-records)
  and [the `ETA_EQUALITY` pragma](https://agda.readthedocs.io/en/v2.9.0/language/coinduction.html#eta-pragma).

* New options `--irrelevance` (default on) and `--no-irrelevance` to allow or
  disallow the irrelevance modality.

* (**BREAKING**.) Now `--erased-matches` takes an optional argument:

  * `--erased-matches=none`: Do not enable any erased matches (this
       can be overridden).

  * `--erased-matches=empty`: Enable erased matches for empty types.

  * `--erased-matches=non-dependent`: Enable erased matches for
    non-indexed, single-constructor types.

  * `--erased-matches=restricted`: Make it possible to import the
    module `Agda.Builtin.Erased.Box-cong`, which contains an
    implementation of `[]-cong` (the type `Erased` can be found in
    `Agda.Builtin.Erased.Erased`):

    ```agda
    record Erased (@0 A : Set a) : Set a where
      no-eta-equality
      constructor [_]
      field
        @0 erased : A

    []-cong : @0 x ≡ y → [ x ] ≡ [ y ]
    []-cong refl = refl
    ```

    In the future `--erased-matches=restricted` might make it possible
    to implement `[]-cong` in user code, but that is currently not
    allowed.

  * `--erased-matches=unrestricted`: Enable unrestricted erased
    matches for single-constructor types. If `--safe` is active, then
    this option is not allowed together with `--without-K`.

  One can also use comma-separated lists of options, for instance
  `--erased-matches=empty,restricted`. This has the same effect as
  giving the options separately (`--erased-matches=empty
  --erased-matches=restricted`). There is no way to turn off something
  that has been enabled, so it does not matter in what order the
  options are given. As an example, `--erased-matches=empty,none`
  means the same thing as `--erased-matches=empty`.

  If none of these options are given, then Agda behaves

  * as if `--erased-matches=none` had been used if `--erasure` is not
    turned on (directly or indirectly), otherwise

  * as if `--erased-matches=empty` had been used if `--without-K` is
    active, and otherwise

  * as if `--erased-matches=empty,unrestricted` had been used.

  Note that these defaults can be overridden by, for instance,
  `--erased-matches=none`.

  The option `--erased-matches` means almost the same thing as
  `--erased-matches=empty,non-dependent` if `--without-K` is active,
  and otherwise it means almost the same thing as
  `--erased-matches=empty,unrestricted`. However, any use of
  `--erased-matches` with explicit arguments takes precedence over
  `--erased-matches` without arguments. For instance,
  `--erased-matches=none --erased-matches` means the same thing as
  `--erased-matches=none`.

  The option `--no-erased-matches` is now a synonym for
  `--erased-matches=none`.

  All variants of `--erased-matches` except for
  `--erased-matches=none` enable `--erasure`.

  This change can lead to some breakage:

  * Previously `--no-erased-matches --erased-matches` meant the same
    thing as `--erased-matches`, now it means the same thing as
    `--erased-matches=none`.

  * Before `--with-K` overrode a previously given
    `--no-erased-matches` and turned on erased matches. That is no
    longer the case.

  Note that the new optional argument to `--erased-matches` is
  experimental: the design might change in the future.

* The new (experimental and possibly unstable) options
  `--erased-funext`, `--erased-propext` and `--erased-quotients`
  enable use of `Agda.Builtin.Erased.Funext`,
  `Agda.Builtin.Erased.Propext` and `Agda.Builtin.Erased.Quotient`,
  respectively.

  All options imply `--erasure`, and `--erased-quotients` implies
  `--erased-funext`.

  These modules contain erased postulates. The idea is that it should
  be safe to use these postulates (under `--safe` and in the absence
  of any Agda bugs):

  * If `--erased-matches=X` is not used, where `X` is one of `empty`,
    `non-dependent`, `restricted` and `unrestricted`, then canonicity
    should hold for non-erased terms (if all opaque definitions are
    made transparent and the context only contains erased
    assumptions).

  * If `--erased-matches=empty` is used, then canonicity should still
    hold if the context plus the postulates are jointly consistent.

  * If `--erased-matches=X` is used, where `X` is one of
    `non-dependent`, `restricted` and `unrestricted`, then reduction
    might get stuck, but compiled programs should still run correctly.

  `Agda.Builtin.Erased.Funext` postulates function extensionality,
  `Agda.Builtin.Erased.Propext` postulates propositional
  extensionality, and `Agda.Builtin.Erased.Quotient` gives access to
  an implementation of set quotients with an eliminator that computes
  for the point constructor.

Errors
------

* Error `ClashingDefinition` now gives the lineage of the previous definition of the same name.
  This helps when it is unclear how this name was imported.  Example:
  ```
    error: [ClashingDefinition]
    Multiple definitions of A. Previous definition
    A is in scope as
      * a postulate Imports.A.A brought into scope by
        - the opening of Imports.A at ...
        - its definition at ...
  ```

* Errors `GenericError` and `GenericDocError` have been replaced by more specific errors.
  (Issue [#7225](https://github.com/agda/agda/issues/7225).)

* New error `NamedWhereModuleUnderWith` for named `where`-modules in clauses
  using with-abstraction; see the entry under _Language_.
  (Issue [#8698](https://github.com/agda/agda/issues/8698).)

* Generalisation failures due to unresolvable dependencies between a
  generalized variable and unsolved metavariables have new, specific
  errors.
  * `GeneralizationPrepruneErrorRefinedContext`, reproduced by Amélia Liao
    (see Issue [#8161](https://github.com/agda/agda/issues/8161#issuecomment-3696949816)).
  * `GeneralizationPrepruneErrorCyclicDependencies`, reproduced by Nils Anders Danielsson
    (see Issue [#3672](https://github.com/agda/agda/issues/3672#issuecomment-482715807)).

* New error `WrongNamedArgumentInLHS` for a named hidden argument on a left hand side
  that does not exist, replacing `WrongHidingInLHS` in this case.
  Like `WrongNamedArgument` on the right hand side, it lists the possible argument names
  (see [#8739](https://github.com/agda/agda/issues/8739)).
  Likewise, error `NoParameterOfName` now lists the possible parameter names.

Warnings
--------

* New warning `UnusedImports` when `open` brings identifiers or modules into scope
  that are definitely not used subsequently.
  A module counts as used if it is referred to,
  e.g. in a qualified name `M.x`, in `open M`, or in `module N = M`.

  If `using` or `renaming` directives are given, or in flavor `-WUnusedImports=all`,
  Agda warns about each name and module that is unused,
  except for modules of data and record types that are not mentioned
  explicitly in the directive.
  If no directive or only a `hiding` directive is given,
  and unless the flavor is `all`,
  Agda only warns if none of the imported names are used.

  Agda also warns about instances brought into scope
  unless `--no-qualified-instances` is on
  (which requires bringing instances into scope if they should be found by instance search).

* `UselessImport` warning instead of parse error when an module is instantiated
  but not opened during `import`, for instance:
  ```agda
  import Structures.IsMonoid Carrier Eq
  ```
  This does not bring module `Structures.IsMonoid` into scope and
  neither any of its exports.
  It either needs an `open` or an `as`-clause such as `as MyMonoid`.

* `UselessPragma` warning instead of hard error `NeedOptionRewriting` when a
  `REWRITE` or `BUILTIN REWRITE` pragma is encountered but `--rewriting` is off.

* Error warning `IllegalDeclarationInDataDefinition` instead of hard error
  when `data` definition contains declarations other than type signatures of
  constructors.

* Error `RecursiveRecordNeedsInductivity` turned into a error warning.

* New warning `DivergentModalityInClause` when modality of a clause diverges
  from that of the function.  Example:
  ```agda
  A : Set₁
  @0 A = Set
  ```

* New warning `InvalidDataOrRecDefParameter` for information (e.g. type, attributes)
  attached to parameters in a `data` or `record` definition (that is separate of its
  data or record signature).
  This replaces errors:
  - `UnexpectedModalityAnnotationInParameter`
  - `UnexpectedTypeSignatureForParameter`

* New warning `InvalidTacticAttribute` for misplaced `@(tactic ...)` attributes.
  This was silently accepted up to Agda 2.8.0 but raises now the new warning:
  ```agda
  postulate
    @(tactic not-in-scope) _ : Set
  ```

* New warning `RewriteVariablesBoundInSingleton` for rewrite rules which bind
  at least one variable exclusively in patterns which might become of singleton
  type after a substitution. Rewrite rules of this form endanger subject
  reduction.
  - Unlike the other warnings about problematic rewrite rules, Agda will still
    try its best to apply rewrites which trigger this warning.
    This is because some very useful rewrite rules unfortunately do not preserve
    subject reduction in the presence of definitional singletons.

* `UnknownNamesInFixityDecl` and `UnknownNamesInPolarityPragmas` are now error warnings.

* The new warning `DefinitionBeforeDeclaration` is emitted if in a classic
  `mutual` block a data/record signature appears *after* the respective
  definition.  This can happen since the nicifier bubbles signatures up.
  (See [issue #8435](https://github.com/agda/agda/issues/8435).)

* New warning `ShouldBeEtaRecordPattern`, raised for
  matches on record constructors in _binders_ (`λ`, `let`, parameter telescopes etc.)
  when the respective record does not have eta.
  For example, this module parameter match triggers the warning:
  ```agda
    record Wrap (A : Set) : Set where
      constructor wrap; no-eta-equality; pattern
      field unwrap : A

    module _ {A} (w@(wrap a) : Wrap A) where
  ```
  Reason for the warning:
  Such a binding is interpreted here as `a = unwrap w`.
  The user expectation that `w` is definitionally equal to `wrap a` is only met if `Wrap` admits `eta-equality`.

  Pattern matching on left hand sides of function definitions does not trigger the warning.

* New warning `FixityDeclarationForNonOperator` when a fixity declaration is attached to a name
  that is neither a pre-, post-, nor infix operator and neither has a pre-, post- or infix `syntax`
  attached to it.
  ```agda
  infixl 10 plus                     -- warning
  plus : ℕ → ℕ → ℕ
  plus = ...

  infix 42 [_]                       -- warning
  [_] : A → List A
  [_] = ...

  infix 255 abs
  syntax abs x = | x |               -- warning

  infix 314 neg                      -- no warning
  syntax neg x = ¬ x

  open import Agda.Builtin.Nat
    renaming (_+_ to infixl 10 add)  -- warning
  ```

* New warning `LibraryVersionConflict` when a project uses different versions of one library
  (see [#8875](https://github.com/agda/agda/issues/8875)).
  The warning shows the dependency tree leading to the conflicting versions
  and the involved `.agda-lib` files:
  ```
  Different versions of the library 'standard-library' depended on:
  [my-project]
    ├─ [standard-library-2.3]
    └─ [my-lib]
        └─ standard-library-2.4 as [standard-library]
  Library files:
  [my-project]: /path/to/my-project/my-project.agda-lib:<line>.<col>-<col>
  [my-lib]: /path/to/my-lib/my-lib.agda-lib:<line>.<col>-<col>
  [standard-library-2.3]: /path/to/agda-stdlib-2.3/standard-library.agda-lib:1:1
  [standard-library]: /path/to/agda-stdlib-2.4/standard-library.agda-lib:1:1
  ```

Syntax
------

Changes to the Agda syntax.

* **Breaking:** The parser will reject ASCII opening delimiters which
  are closed by a Unicode delimiter, and vice-versa. Concretely, this
  means the mismatched pairs `⦃ ... }}`/`{{ ...  ⦄` and
  `⦇ … |)`/`(| … ⦈` are now parse errors.

* Modality annotations in aliases and let-bindings are now supported
  (PR [#7990](https://github.com/agda/agda/pull/7990)).
  Example:
  ```agda
    split : {A B C : Set} (@0 p : A × B) (k : @0 A → @0 B → C) → C
    split p k = let @0 (x , y) = q in k x y
      where
      @0 q = p
  ```

* Postfix projections cannot be surrounded by parentheses anymore.
  E.g. these postfix projection applications are now illegal in expressions:
  ```agda
    r (.proj)
    r .(proj)
  ```

* Idiom brackets and `do` notation may now appear *qualified*, as in
  `M.do` or `M.(| f x y z |)`, in which case the functions needed for
  desugaring these are looked up in `M` rather than in the surrounding
  scope ([PR #8280](https://github.com/agda/agda/pull/8280)).

Language
--------

Changes to type checker and other components defining the Agda language.

* (**BREAKING**) Named `where`-modules (`module M where`) are no longer
  allowed in clauses that use with-abstraction, i.e. clauses with `with`,
  `rewrite`, or `with p ← e`.  Such a clause is now rejected with the new
  error `NamedWhereModuleUnderWith`:
  ```agda
  f : Bool → Bool
  f x with x
  ... | true  = local
    module M where   -- rejected
    local = false
  ... | false = true
  ```
  With-abstraction can change the types of the module parameters that `M`
  inherits from its parent module, so the telescope of `M` lies about them.
  Since `M` is visible outside of the clause, it could then be instantiated
  with ill-typed arguments, which allowed a proof of `⊥`.

  Ordinary anonymous `where`-blocks are unaffected, and so is
  `using p ← e`, which does not with-abstract but introduces a let-binding.
  (Issue [#8698](https://github.com/agda/agda/issues/8698).)

* (**BREAKING**) The pseudo-name `R.constructor`, which refers to the
  constructor of record `R`, is now resolved by the ordinary scope lookup:
  `constructor` is a name bound in the record module `R`.
  (It can never be written unqualified, since `constructor` is a keyword;
  in particular, `open R` does not bring it into scope, and a module
  application `module M = R` does not provide `M.constructor`.)

  Consequently, the qualification `R` in `R.constructor` is now interpreted
  as the name of the record *module* rather than the name of the record
  *type*.  Thus, this now succeeds:
  ```agda
  module M where
    record R : Set where

  open M using (module R)

  t = R.constructor   -- used to fail
  ```
  while this now fails:
  ```agda
  module M where
    record R : Set where

  open M using (R) hiding (module R)

  t = R.constructor   -- used to succeed
  ```

  This also fixes [Issue #8625](https://github.com/agda/agda/issues/8625):
  an internal error when referring to `R.constructor` from the interaction
  top level.

* (**BREAKING**): In the presence of `--erasure`, types of lambdas expressions
  are not inferred unless every lambda-bound variable has been given its erasure
  status (`@0` or `@ω`) explicitely.
  The reason is that otherwise Agda might infer the wrong erasure status, see, e.g.,
  [Issue #7001](https://github.com/agda/agda/issues/7001).

  Now we have the following behavior:
  ```agda
    fails    = λ x → x + x
    succeeds = λ (@ω x) → x + x
    alsoOK   = λ (@ω A : Set) (@0 B : Set) → A
  ```
  With that change `--erasure` gets more akin to Cubical Agda that categorically
  refuses to infer lambdas (since they could construct either functions or paths).

* (**BREAKING**): Instance search will no longer eta-expand non-instance
  (visible and hidden) variables of record type in the context to find
  instance fields ([PR #8367](https://github.com/agda/agda/pull/8367)).

  This change means that instance search can now happen even when the types of
  non-instance arguments are yet-unsolved metavariables. Specifically, instance
  search now works in functions with a type signature of the form `∀ x → ...`,
  where previously it would require the type of `x` to be annotated.

  It also means that instance search no longer requires head-normalising the
  types of non-instance function arguments, which may have a positive effect on
  type checking performance.

  Due to this change, code that relied on eta-expanding visible argument (like
  `r : R` in the example below) to find the instance field will no longer work.

  ```agda
  postulate
    T : Set
    use : ⦃ t : T ⦄ → Set

  record R : Set where
    field ⦃ inst ⦄ : T

  fails : R → Set
  fails r = use
  ```

  In this case the code can be repaired by explicitly eta-expanding the record
  pattern:

  ```agda
  succeeds : R → Set
  succeeds r@record{} = use -- or just record{}, if r is unused
  ```

  In other cases more substantial changes might be required. For example, in the
  code below the record values `Aa` and `Bb` are parameters so they cannot be
  eta-expanded directly:

  ```agda
  record IsPointed (A : Set) : Set where
    field
      point : A
  open IsPointed {{...}}

  record PointedSet : Set1 where
    field
      Carrier : Set
      {{IsPointed[Carrier]}} : IsPointed Carrier
  open PointedSet

  record PointedFunction (Aa Bb : PointedSet) : Set where
    field
      run : Aa .Carrier -> Bb .Carrier
      preserves-point : run point ≡ point
  ```

  Here it is possible to work around the problem by marking the projection
  `IsPointed[Carrier]` as an `instance` and then applying the record module
  `PointedSet` to the respective values `Aa` and `Bb`:

  ```agda
  record PointedSet : Set1 where
    field
      Carrier : Set
      instance
        {{IsPointed[Carrier]}} : IsPointed Carrier
  open PointedSet

  record PointedFunction (Aa Bb : PointedSet) : Set where
    open PointedSet Aa renaming (Carrier to AA)
    open PointedSet Bb renaming (Carrier to BB)
    field
        run : AA -> BB
        preserves-point : run point ≡ point
  ```

  In general, instance search is intended to work well with unbundled structures
  such as `IsPointed`, while using it with bundled structures such as
  `PointedSet` might require some more creative workarounds such as the one
  above.

* Instance search now finds instance fields in *functions* that produce
  eta records ([Issue #8337](github.com/agda/agda/issues/8337)), as
  long as these functions are in the context with instance visibility.

  In effect, this means that a family of instances of a "subclass" also
  provides a family of instances for the "superclass". For example, the
  following code is now accepted:

  ```agda
  record Eq (A : Set) : Set where
    field
      _==_ : A → A → Bool

  record Ord (A : Set) : Set where
    field
      ⦃ eq ⦄ : Eq A
      _<=_ : A → A → Bool

  open Ord ⦃ ... ⦄
  open Eq ⦃ ... ⦄

  test
    : {I : Set} {F : I → Set} ⦃ ordi : ∀ {i} → Ord (F i) ⦄
    → (i : I) → F i → F i → Bool
  test i x y = x == y
  ```

* Functions defined using with-abstraction equality (`with … in eq`) can now be
  reasoned about using the same with-abstraction equality: the equality proof
  is correctly generalised over. This should make most (if not all) uses of the
  old-style `inspect` idioms for the built-in equality type unnecessary.

* Added support for [Cubical Agda without Glue Types](https://agda.readthedocs.io/en/v2.9.0/language/cubical.html#cubical-agda-without-glue)
  by using the flag `--cubical=no-glue`,
  a variant of Cubical Agda which disables the Glue types.
  For compatibility with modules using `--cubical[=full]` and `--cubical=erased`, see
  [variants](https://agda.readthedocs.io/en/v2.9.0/language/cubical.html#variants).

* Added the [Sharp modality](https://agda.readthedocs.io/en/v2.9.0/language/flat.html#the-sharp-modality),
  which adds a right adjoint to the existing flat modality enabled via the
  `--cohesion` flag. This also enables the use of attributes in record
  fields for any cohesion modality which has a left adjoint (currently
  just sharp and continuous).

Builtins
--------

* (**BREAKING**): The fixity declarations for `Agda.Builtin.Int.pos` and for
  `primINeg`, `primIMin`, and `primIMax`, in `Agda.Primitive.Cubical` have been removed.
  Reason: they trigger the new warning `FixityDeclarationForNonOperator`.
  If you want to use these builtins as operators, supply a fixity in the `renaming` directive, e.g.:
  ```agda
  open import Agda.Builtin.Int renaming (pos to infix 8 +_)
  open import Agda.Primitive.Cubical renaming
    ( primINeg to infix  30 ~_
    ; primIMin to infixr 20 _∧_
    ; primIMax to infixr 20 _∨_
    )
  ```

Reflection
----------

* `tcTypeError` now throws `UserError` instead of `GenericDocError`.

* Tactic arguments (`@tactic`) are now supported in module telescopes.

* `unquoteDecl` and `unquoteDef` now check that the meta-program
  actually defines all the given identifiers
  (issue [#8851](https://github.com/agda/agda/issues/8851)).

Library management
------------------

* Suppport for version-specific `defaults` files: a file whose name is
  of the form `defaults-X.Y.Z` will take precedence over the standard
  `defaults` one for the `X.Y.Z` version of the compiler. This can be
  used to have default libraries that are only compatible with a given
  version of the compiler.

Interaction and emacs mode
--------------------------

* The JSON interaction protocol (`--interaction-json`) no longer loses
  information that the Emacs frontend displays:

  - `GoalAndHave` responses now include a `boundary` field with the
    boundary faces of the checked expression
    ("Boundary (actual)" in the Emacs mode).

  - `NormalForm` and `InferredType` responses now pretty-print the
    expression in the command state captured when the command ran, as
    the Emacs frontend does, instead of in the current state
    (fixes [Issue #5665](https://github.com/agda/agda/issues/5665)).

  - `Mimer` responses now include the `interactionPoint` the solution
    refers to.

* Proof search (Mimer, `C-c C-a` in Emacs) now also uses functions
  defined in the same `mutual` block as the function being defined,
  without having to give them as hints.
  As for recursive calls to the function itself, they are only applied
  to structurally smaller arguments
  (Issue [#8783](https://github.com/agda/agda/issues/8783)).

* Syntax highlighting and go-to-definition now also works in the Agda
  information and debug buffers in Emacs where goals etc. are displayed.
  This fixes long-standing [Issue #706](https://github.com/agda/agda/issues/706).

* By temporarily turning on printing of hidden arguments
  (`OPTION --show-implicit`, `C-c C-x C-h` in Emacs)
  and then splitting on result in a hole
  (`C-c C-c RET` in Emacs, the whole sequence being `C-c C-x C-h C-c C-c RET`),
  hidden arguments can be introduced in the left hand side of a clause.
  In the presence of generalized variables, this used to introduce unparsable names.
  For instance:
  ```agda
    variable
      l : Level
      A : Set l

    id : A → A
    id = {!!}
  ```
  Here, `id {A.l} {A} x = ?` was produced, triggering an error.
  Now, the correct `id {A = A} x = ?` is produced
  (Issue [#8153](https://github.com/agda/agda/issue/8153)).

* The implicit (hidden and instance) fields of a record pattern are
  no longer printed by default.
  They are only printed with option `--show-implicit`
  (`C-c C-x C-h` in Emacs), or if the user wrote them in the first place.
  For instance, case splitting on `x` in
  ```agda
    record R : Set where
      field
        {n} : Nat
        rf  : n ≡ n

    f : R → Set
    f x = {!x!}  -- C-c C-c x
  ```
  now produces `f record { rf = rf } = ?` instead of
  `f record { n = n ; rf = rf } = ?`.
  This conforms the treatment of record patterns to the
  situation where the record type has a constructor, in which case the
  hidden arguments were already omitted
  (Issue [#8787](https://github.com/agda/agda/issue/8787)).

* Catch-all copattern clauses are now tolerated as unreachable clauses
  rather than being outright rejected with a `CosplitCatchall` error.
  They can be used as jumpboard for further result splitting.
  (A scenario is a record type that got extended with new fields,
  and definitions producing record values need to be extended as well.)
  Example:
  ```agda
    test : Σ A B
    test .fst = a
    test = {!!}  -- C-c C-c RET
  ```
  This split produces the clause `test .snd = ?`.
  (Issue [#8139](https://github.com/agda/agda/issue/8139)).


* A normalization level can now also passed to command `Cmd_constraints`
  ("show constraints", `C-c C-=` in Emacs).
  In Emacs, the normalization level is given as usual by `C-u` prefixes.

  This interface change is **breaking** for frontends to `agda --interaction`
  such as the VSCode `agda-mode`, which need updating.

* Fixed an internal error in `Cmd_helper_function` (`C-c C-h` in Emacs)
  (Issue [#8103](https://github.com/agda/agda/issue/8103)).
  Changed the type of `Goal_HelperFunction` which might be **breaking**
  3rd-party interaction frontends.

* `NON_TERMINATING` functions now only reduce in `IgnoreAbstract` mode of
  commands `Cmd_compute(_toplevel)` (`C-u C-c C-n` in Emacs)
  regardless of whether invoked at toplevel or in a hole
  (Issue [#2410](https://github.com/agda/agda/issue/2410)).

* _Go-to-definition_ (`M-.`) is now implemented using Emacs' built-in
  [Xref].  Basic usage stays the same (`M-.` or using the mouse), but
  now also includes searching for definitions by exact (`C-u M-.`) or
  approximate names (`C-M-.`) and listing references (`M-?`) in loaded
  files.

[Xref]: https://www.gnu.org/software/emacs/manual/html_node/emacs/Xref.html

Backends
--------

* `agda --html --html-highlight=code example.lagda.tree` now produces
  `html/example.tree`, which Forester can consume directly;
  no external tools needed.

* New option `--ghc-trace` for GHC Backend to instrument code
  such that the Agda name of the function is printed to `stderr`
  whenever a function is entered.

* The JS backend now explicitly lists all primitives that should compile
  to `undefined`. Primitives not in this list or the RTS trigger a new
  `UnknownJSPrimitive` warning
  (see [#8352](https://github.com/agda/agda/issues/8352)).

* The JS backend's CJS & AMD module styles are now deprecated.
  Please use ES6 module style instead (`--js-es6`).

* The JS backend now compiles constructors to string-tagged arrays.
  This change is **breaking** for hand-written JS code relying on the previous Scott-Encoding.
  Constructors for types with `COMPILE JS` pragmas are not affected.
  (see [#8720](https://github.com/agda/agda/pull/8720))

Issues closed
-------------

For 2.9.0, the following issues were
[closed](https://github.com/agda/agda/issues?q=is%3Aissue+milestone%3A2.9.0+is%3Aclosed)
(see [bug tracker](https://github.com/agda/agda/issues)):

### Consistency issues

- [Issue #7892](https://github.com/agda/agda/issues/7892): The telescope of a projection need not be the telescope of the record type
- [Issue #8341](https://github.com/agda/agda/issues/8341): Postulates in safe mode (regression in 2.8.0)
- [Issue #8453](https://github.com/agda/agda/issues/8453): False because the `SIGMA` builtin accepts types that are not Σ-types
- [Issue #8557](https://github.com/agda/agda/issues/8557): Proof of global choice and of false
- [Issue #8564](https://github.com/agda/agda/issues/8564): Function call tricks positivity checker
- [Issue #8565](https://github.com/agda/agda/issues/8565): Positivity bug with builtins
- [Issue #8587](https://github.com/agda/agda/issues/8587): Endpoints of paths are not checked without `--cubical`
- [Issue #8683](https://github.com/agda/agda/issues/8683): Cubical primitive side conditions are not checked when an application is inferred
- [Issue #8686](https://github.com/agda/agda/issues/8686): Projection-likeness drops arguments the principal argument's type does not determine
- [Issue #8687](https://github.com/agda/agda/issues/8687): The coverage checker infers missing clauses under the wrong module-parameter substitution
- [Issue #8688](https://github.com/agda/agda/issues/8688): Occurrence analysis ignores sorts: a Level argument used only in Set l is Nonvariant, giving universe resizing
- [Issue #8694](https://github.com/agda/agda/issues/8694): The unifier's cycle check looks inside irrelevant and Prop-typed constructor arguments
- [Issue #8695](https://github.com/agda/agda/issues/8695): The unifier's cycle rule checks only the head constructor for higher inductive types
- [Issue #8696](https://github.com/agda/agda/issues/8696): Data/record types copied by a module application inside a block get their arguments marked unused
- [Issue #8697](https://github.com/agda/agda/issues/8697): Interface serialiser conflates the Float literals 0.0 and -0.0
- [Issue #8698](https://github.com/agda/agda/issues/8698): Inconsistency with named `where` modules under `with` (regression in 2.5.2)
- [Issue #8699](https://github.com/agda/agda/issues/8699): Termination checker descends into irrelevant constructor arguments of dot patterns
- [Issue #8700](https://github.com/agda/agda/issues/8700): Clause-based matcher treats a MissingClauses-stuck argument as a definite mismatch (regression in 2.6.3)
- [Issue #8703](https://github.com/agda/agda/issues/8703): Clause-based reduction skips underapplied clauses, reducing differently than after compilation to case-trees
- [Issue #8704](https://github.com/agda/agda/issues/8704): Clause-based reduction falls through on a stuck lazy (forced) match, disagreeing with the case tree (regression in 2.7.0)
- [Issue #8834](https://github.com/agda/agda/issues/8834): Escape from sharp modality / negativity

### Internal errors

- [Issue #3123](https://github.com/agda/agda/issues/3123): Malformed projection definition
- [Issue #6173](https://github.com/agda/agda/issues/6173): Internal error at Agda/Syntax/Abstract/Name.hs:150:44 (regression in 2.6.2)
- [Issue #6770](https://github.com/agda/agda/issues/6770): Incorrect substitution when opening parameterised module with a generalised variable.
- [Issue #7564](https://github.com/agda/agda/issues/7564): Internal error when giving the unit type in a function on HITs
- [Issue #7629](https://github.com/agda/agda/issues/7629): Internal error with src/full/Agda/TypeChecking/Substitute.hs:140:33 using Cubical Agda
- [Issue #7964](https://github.com/agda/agda/issues/7964): Synthesis fails when given hint from a module opened as an instance
- [Issue #8068](https://github.com/agda/agda/issues/8068): `__IMPOSSIBLE__` on dependent pattern match + unrelated holes
- [Issue #8097](https://github.com/agda/agda/issues/8097): Internal error when trying Automatic Proof Search (regression in 2.8.0)
- [Issue #8103](https://github.com/agda/agda/issues/8103): Internal error when trying C-c C-h (helper function)
- [Issue #8215](https://github.com/agda/agda/issues/8215): Internal error triggered by instance declaration within record (regression in 2.8.0)
- [Issue #8263](https://github.com/agda/agda/issues/8263): Internal error in ProjectionLike.hs (regression in 2.6.4)
- [Issue #8298](https://github.com/agda/agda/issues/8298): `__IMPOSSIBLE__` for incomplete mixfix copattern definition in let binding (regression in 2.8.0)
- [Issue #8325](https://github.com/agda/agda/issues/8325): An internal error during refining (src/full/Agda/TypeChecking/Monad/Context.hs:672:26) (regression in 2.8.0)
- [Issue #8336](https://github.com/agda/agda/issues/8336): Internal error in double checker with projection-like functions (Non-exhaustive patterns in Just n) (regression in 2.6.4)
- [Issue #8365](https://github.com/agda/agda/issues/8365): Crash with `--rewriting` flag
- [Issue #8514](https://github.com/agda/agda/issues/8514): `__IMPOSSIBLE__` involving local rewrite rule and a with abstraction
- [Issue #8521](https://github.com/agda/agda/issues/8521): `__IMPOSSIBLE__` when pattern matching against irrelevant instance argument? (regression in 2.6.2)
- [Issue #8532](https://github.com/agda/agda/issues/8532): Missing in reduce in anti-unification causes `__IMPOSSIBLE__` in `TypeChecking/Reduce/Fast.hs:1417:43` (regression in 2.5.3)
- [Issue #8545](https://github.com/agda/agda/issues/8545): Internal error with instance and open-public in record (regression in 2.5.2)
- [Issue #8554](https://github.com/agda/agda/issues/8554): `__IMPOSSIBLE__` in Agda.TypeChecking.MetaVars triggered interactively
- [Issue #8577](https://github.com/agda/agda/issues/8577): IMPOSSIBLE during pattern matching in the presence of a local rewrite rule
- [Issue #8580](https://github.com/agda/agda/issues/8580): Unused implicit parameter in pattern synonym `__IMPOSSIBLE__`
- [Issue #8581](https://github.com/agda/agda/issues/8581): Internal error in TypeChecking/Monad/Context.hs when trying to load/type-check a malformed lambda parameter pattern inside an interaction hole
- [Issue #8621](https://github.com/agda/agda/issues/8621): Internal error (maybe related to instance arguments?) (regression in 2.8.0)
- [Issue #8625](https://github.com/agda/agda/issues/8625): agda2-infer-type-maybe-toplevel on anonymous record constructor causes an internal error
- [Issue #8626](https://github.com/agda/agda/issues/8626): `__IMPOSSIBLE__` at `Agda/TypeChecking/CompiledClause/Compile.hs`:180:20
- [Issue #8634](https://github.com/agda/agda/issues/8634): In Emacs, unknown `.agda-lib` field triggers `__IMPOSSIBLE__` at `Agda.TypeChecking.Serialise.Instances.Common`:101:34 (regression in 2.8.0)
- [Issue #8636](https://github.com/agda/agda/issues/8636): Internal error when an instance value is used as an index
- [Issue #8649](https://github.com/agda/agda/issues/8649): Internal error in confluence checker with rewrite rule for coinductive record projection
- [Issue #8680](https://github.com/agda/agda/issues/8680): Impossible state when unused pattern argument is also a variable declaration
- [Issue #8777](https://github.com/agda/agda/issues/8777): Crash due to unsound call to `canonicalName`
- [Issue #8808](https://github.com/agda/agda/issues/8808): Internal error during cubical boundary recovery
- [Issue #8851](https://github.com/agda/agda/issues/8851): `unquoteDecl` panics when the macro does not `declareDef` at all
- [Issue #8853](https://github.com/agda/agda/issues/8853): Internal error when using `withReconstructed`

### Other regressions

- [Issue #3054](https://github.com/agda/agda/issues/3054): Reduction missing during LHS checking (regression in 2.6.0)
- [Issue #4150](https://github.com/agda/agda/issues/4150): Not in scope error instead of missing type signature error (regression in 2.5.4)
- [Issue #7595](https://github.com/agda/agda/issues/7595): `with` compiles 40x slower than `case_of_` (regression in 2.6.4.2)
- [Issue #8094](https://github.com/agda/agda/issues/8094): Backends that are enabled by default can no longer print help (regression in 2.8.0)
- [Issue #8096](https://github.com/agda/agda/issues/8096): Performance regression for test/Succeed/Issue6097-5 (regression in 2.6.4)
- [Issue #8150](https://github.com/agda/agda/issues/8150): Generate helper function reorders arguments (regression in 2.6.1, regression in 2.6.4)
- [Issue #8168](https://github.com/agda/agda/issues/8168): Mimer triggers a ParseError (regression in 2.8.0)
- [Issue #8300](https://github.com/agda/agda/issues/8300): Instanceness of principal argument dropped by postfix projection (regression in 2.6.0)
- [Issue #8435](https://github.com/agda/agda/issues/8435): In `mutual` blocks `data`/`record` signatures can be given after their definition (regression in 2.6.0)
- [Issue #8559](https://github.com/agda/agda/issues/8559): Copattern definition gives UnequalTerms for equal terms (regression in 2.6.0)
- [Issue #8771](https://github.com/agda/agda/issues/8771): Regression in 2.6.4 with `--projection-like` (regression in 2.6.4)
- [Issue #8811](https://github.com/agda/agda/issues/8811): Can't give: `metaOccurs` check too strict with `--prop`, `--polarity`, or `--experimental-irrelevance` (regression in 2.6.2)

### Other issues

- [Issue #706](https://github.com/agda/agda/issues/706): syntax highlighting and definition location etc. for definitions in goal/error buffer
- [Issue #1120](https://github.com/agda/agda/issues/1120): Improve operator parsing performance
- [Issue #1680](https://github.com/agda/agda/issues/1680): Simple termination checking fails with --without-K
- [Issue #2369](https://github.com/agda/agda/issues/2369): “Module cannot be imported since it has open interaction points” should always point to module
- [Issue #2410](https://github.com/agda/agda/issues/2410): `C-c C-n` unfolds non-terminating functions
- [Issue #2503](https://github.com/agda/agda/issues/2503): On warning about redundant imports
- [Issue #2591](https://github.com/agda/agda/issues/2591): Operator parse error should be scope error
- [Issue #2636](https://github.com/agda/agda/issues/2636): The positivity checker complains when a new definition is added in the same where clause
- [Issue #3218](https://github.com/agda/agda/issues/3218): termination checking failure in copattern-style definition
- [Issue #3355](https://github.com/agda/agda/issues/3355): NO_POSITIVITY_CHECK pragma ignored in local `where` block
- [Issue #3677](https://github.com/agda/agda/issues/3677): Operator parse error should include "nullary operators"
- [Issue #4228](https://github.com/agda/agda/issues/4228): Wrong context for solved interaction point in generalized type
- [Issue #4271](https://github.com/agda/agda/issues/4271): Make module names into links in error messages
- [Issue #4339](https://github.com/agda/agda/issues/4339): Qualified `do` (Resolving the monad instance for `do` notation)
- [Issue #5305](https://github.com/agda/agda/issues/5305): Generalisation fails with --no-syntactic-equality
- [Issue #5411](https://github.com/agda/agda/issues/5411): `open` in module telescope goes wrong with generalization
- [Issue #5524](https://github.com/agda/agda/issues/5524): duplicate identifiers ignored in fixity declarations
- [Issue #5618](https://github.com/agda/agda/issues/5618): More precise wording of warning "Instance applies only to declarations that introduce new identifiers"
- [Issue #5665](https://github.com/agda/agda/issues/5665): agda --interaction-json gives unnecessarily qualified names after opening modules
- [Issue #5670](https://github.com/agda/agda/issues/5670): OperatorsExpr parsing blows up on large file
- [Issue #5791](https://github.com/agda/agda/issues/5791): Error message only mentions .agda and .lagda
- [Issue #5808](https://github.com/agda/agda/issues/5808): --interaction-json: interaction points with empty ranges after refine
- [Issue #5836](https://github.com/agda/agda/issues/5836): JSON interaction doesn't give ranges for newly refined goals
- [Issue #5839](https://github.com/agda/agda/issues/5839): Incorrect usage of underscore in names breaks parsing
- [Issue #6198](https://github.com/agda/agda/issues/6198): Canonicity failure with --cubical (?)
- [Issue #6240](https://github.com/agda/agda/issues/6240): Weird type generated for record field opened in telescope with generalized variable
- [Issue #6425](https://github.com/agda/agda/issues/6425): Not-in-scope constructors make patterns parse-failed
- [Issue #6825](https://github.com/agda/agda/issues/6825): Irrefutable matching in binders does not deliver expected results for non-eta patterns
- [Issue #6847](https://github.com/agda/agda/issues/6847): On dropping GHC versions 9.0 and lower
- [Issue #6861](https://github.com/agda/agda/issues/6861): Parallelize build
- [Issue #6939](https://github.com/agda/agda/issues/6939): Non-dependent tactic argument fails to run tactic
- [Issue #6940](https://github.com/agda/agda/issues/6940): Add flag to direct output of GHC backend
- [Issue #7001](https://github.com/agda/agda/issues/7001): Agda treats lambdas that are not annotated with `@ω` as non-erased
- [Issue #7139](https://github.com/agda/agda/issues/7139): Mangled trX/Con clause for indexed type with green slime
- [Issue #7225](https://github.com/agda/agda/issues/7225): Named errors instead of Generic[Doc]Error
- [Issue #7562](https://github.com/agda/agda/issues/7562): The script `install_agda_user.bat` for Windows uses the dangerous `setx` command
- [Issue #7664](https://github.com/agda/agda/issues/7664): Agda ignores constructor parameters but only if they're copied under a parameterised module
- [Issue #7691](https://github.com/agda/agda/issues/7691): Custom treeless pipeline is ignored for "recursive" calls
- [Issue #7805](https://github.com/agda/agda/issues/7805): Inscrutable error with `record where` + implicit arguments
- [Issue #7829](https://github.com/agda/agda/issues/7829): Fields with signature not highlighted in `record where`
- [Issue #7836](https://github.com/agda/agda/issues/7836): `record where` silently ignores postulated field values
- [Issue #7837](https://github.com/agda/agda/issues/7837): `record where` handles duplicate names in open directive in non-standard way
- [Issue #7838](https://github.com/agda/agda/issues/7838): `record where`'s interpretation of `open` is very syntactic
- [Issue #7876](https://github.com/agda/agda/issues/7876): Internal error with `--rewriting` and dependent identity type
- [Issue #7893](https://github.com/agda/agda/issues/7893): Confluence check misses critical pair
- [Issue #7906](https://github.com/agda/agda/issues/7906): Manually eta-expanding clause makes termination checking fail
- [Issue #7941](https://github.com/agda/agda/issues/7941): Denial of case split in the presence of known values
- [Issue #7968](https://github.com/agda/agda/issues/7968): Undefined `Char`-related primitives when compiled to JS
- [Issue #7972](https://github.com/agda/agda/issues/7972): Mimer has problems instantiating predicates
- [Issue #7976](https://github.com/agda/agda/issues/7976): Soft error for `{-# REWRITE ... #-}` without `--rewriting`
- [Issue #7987](https://github.com/agda/agda/issues/7987): Allow erased `let`s
- [Issue #7988](https://github.com/agda/agda/issues/7988): Declarations before top-level module in a library give wrong error message
- [Issue #7989](https://github.com/agda/agda/issues/7989): Weird error for irrelevant clause
- [Issue #7994](https://github.com/agda/agda/issues/7994): `tactic` attributes at declarations are parsed, then silently dropped
- [Issue #7998](https://github.com/agda/agda/issues/7998): `instance` silently dropped from `primitive` and `variable` blocks
- [Issue #8016](https://github.com/agda/agda/issues/8016): Nix build fails on aarch64-darwin
- [Issue #8033](https://github.com/agda/agda/issues/8033): Coloring lost in warnings
- [Issue #8035](https://github.com/agda/agda/issues/8035): Optimising module copying
- [Issue #8037](https://github.com/agda/agda/issues/8037): checkParameters is defeated by not copying the record
- [Issue #8048](https://github.com/agda/agda/issues/8048): Guarded Cubical: Using instance arguments for tick variables enables proving join
- [Issue #8074](https://github.com/agda/agda/issues/8074): GHC 9.14
- [Issue #8078](https://github.com/agda/agda/issues/8078): piSort case of documentation
- [Issue #8080](https://github.com/agda/agda/issues/8080): std-lib-test spends ~5% of runtime rendering warnings that are never displayed
- [Issue #8092](https://github.com/agda/agda/issues/8092): COMPILE pragmas on declared-but-not-yet-defined symbols are discarded
- [Issue #8098](https://github.com/agda/agda/issues/8098): Agda deletes read-only interface files
- [Issue #8100](https://github.com/agda/agda/issues/8100): Non-normalized level printed for interactive "show constraints" and "solve"
- [Issue #8105](https://github.com/agda/agda/issues/8105): For ClashingDefinition also highlight the first definition
- [Issue #8112](https://github.com/agda/agda/issues/8112): Can not eliminate [type blocked on meta] forces very silly extended lambdas
- [Issue #8126](https://github.com/agda/agda/issues/8126): Generalizable `variable`s presented as projections in error message
- [Issue #8128](https://github.com/agda/agda/issues/8128): Poor error for duplicate definition in mutual block
- [Issue #8132](https://github.com/agda/agda/issues/8132): Error SolvedButOpenHoles should provide means to jump to module with open goals
- [Issue #8134](https://github.com/agda/agda/issues/8134): Caching is broken
- [Issue #8139](https://github.com/agda/agda/issues/8139): Fail soft on catch-all for copatterns
- [Issue #8144](https://github.com/agda/agda/issues/8144): Improve error message when trying to open record in a mutual block
- [Issue #8153](https://github.com/agda/agda/issues/8153): Result splitting should not introduce indirectly generalized variables
- [Issue #8157](https://github.com/agda/agda/issues/8157): Case split makes instance clause vanish
- [Issue #8170](https://github.com/agda/agda/issues/8170): Increase `--termination-depth` to 2 or infinity
- [Issue #8171](https://github.com/agda/agda/issues/8171): "Failed to give"  with `--polarity`
- [Issue #8191](https://github.com/agda/agda/issues/8191): [ question/bug ] are infix names allowed for parametrised modules?
- [Issue #8206](https://github.com/agda/agda/issues/8206): `interleaved mutual` does not check consistency of parameters (hiding / typing)
- [Issue #8218](https://github.com/agda/agda/issues/8218): Unequal terms despite rewrite rule (across modules)
- [Issue #8228](https://github.com/agda/agda/issues/8228): Parse Error with Display Pragma and Mixfix Operator
- [Issue #8231](https://github.com/agda/agda/issues/8231): Rewrite rule matching does not respect irrelevance
- [Issue #8249](https://github.com/agda/agda/issues/8249): Literate Markdown: Option to only treat `agda`-code blocks as agda code
- [Issue #8256](https://github.com/agda/agda/issues/8256): `M-.` does not work in the information buffer
- [Issue #8269](https://github.com/agda/agda/issues/8269): Documentation: Is ETA for Colists Safe?
- [Issue #8273](https://github.com/agda/agda/issues/8273): Confluence Checking Error After Reloading File/Importing
- [Issue #8281](https://github.com/agda/agda/issues/8281): Literate programming Forester potential improvement
- [Issue #8308](https://github.com/agda/agda/issues/8308): Support turning off colored output via `NO_COLOR` environment variable
- [Issue #8312](https://github.com/agda/agda/issues/8312): `with … in` functions cannot reason about themselves
- [Issue #8326](https://github.com/agda/agda/issues/8326): Importing file with --cubical reports error about --two-level
- [Issue #8327](https://github.com/agda/agda/issues/8327): Splitting on a prop in between record fields fails with `SplitInProp` error
- [Issue #8337](https://github.com/agda/agda/issues/8337): Agda instance search cannot find nested instances
- [Issue #8344](https://github.com/agda/agda/issues/8344): C-c C-, shows a binding that is not there
- [Issue #8352](https://github.com/agda/agda/issues/8352): JS backend: unknown primitives silently compiled to Undefined
- [Issue #8370](https://github.com/agda/agda/issues/8370): Putting a `pattern` `record` in an index kills canonicity for cubical
- [Issue #8374](https://github.com/agda/agda/issues/8374): Allow fixity decls for anonymous modules outside module
- [Issue #8380](https://github.com/agda/agda/issues/8380): Weird behavior with comment parsing
- [Issue #8388](https://github.com/agda/agda/issues/8388): `in`  suggests to use no longer used {-# BUILTIN REFL name #-}
- [Issue #8398](https://github.com/agda/agda/issues/8398): JS backend: use tagged arrays instead of Scott encoding for data types
- [Issue #8400](https://github.com/agda/agda/issues/8400): No error highlighting for InstanceWithExplicitArg
- [Issue #8402](https://github.com/agda/agda/issues/8402): LaTeX backend uses unknown command`\AgdaDeadcode`
- [Issue #8420](https://github.com/agda/agda/issues/8420): Direct support for `[]-cong`
- [Issue #8431](https://github.com/agda/agda/issues/8431): Error RecursiveRecordNeedsInductivity switched off by NO_POSITIVITY_CHECK
- [Issue #8440](https://github.com/agda/agda/issues/8440): Cubical Agda prints `IsOne (A ∨ ~ A)` in an error where `A : Set`
- [Issue #8478](https://github.com/agda/agda/issues/8478): Lines/second in profiling output
- [Issue #8479](https://github.com/agda/agda/issues/8479): Agda.Interaction.InteractionTop highlights the fatal import in the wrong buffer
- [Issue #8494](https://github.com/agda/agda/issues/8494): Emacs mode gets confused on goal position with certain strings
- [Issue #8495](https://github.com/agda/agda/issues/8495): Emacs goals are non-interactive in literate forester files
- [Issue #8519](https://github.com/agda/agda/issues/8519): Rewrite rule does not apply after doing a path abstraction on LHS
- [Issue #8526](https://github.com/agda/agda/issues/8526): ETA pragma silently does nothing for imported (coinductive) records
- [Issue #8529](https://github.com/agda/agda/issues/8529): Bug (cut-and-paste error) allows NO_UNIVERSE_CHECK to attach to mutual blocks
- [Issue #8570](https://github.com/agda/agda/issues/8570): Meta-variable instantiated with ill-resourced type
- [Issue #8583](https://github.com/agda/agda/issues/8583): (Co)InfectiveImport error should provide jumpable link to imported module
- [Issue #8591](https://github.com/agda/agda/issues/8591): Quotient types, erased function and propositional extensionality
- [Issue #8596](https://github.com/agda/agda/issues/8596): Termination checker rejects program when field takes 2 or 4 (but not 0, 1, 3, 5, or 6) trivial ⊤ arguments
- [Issue #8599](https://github.com/agda/agda/issues/8599): [ with ] nested irrefutable `with`s cause a parse error!?
- [Issue #8638](https://github.com/agda/agda/issues/8638): GHC backend erases patterns on datatypes indexed by erased datatypes
- [Issue #8639](https://github.com/agda/agda/issues/8639): JS backend mis-compiles list cons (`_∷_`)
- [Issue #8647](https://github.com/agda/agda/issues/8647): FOREIGN GHC pragma changes lost by caching
- [Issue #8666](https://github.com/agda/agda/issues/8666): Make `--irrelevance` infective
- [Issue #8710](https://github.com/agda/agda/issues/8710): The second imported rewriting relation is ignored
- [Issue #8739](https://github.com/agda/agda/issues/8739): Error "unexpected implicit argument" should print the available implicit arguments
- [Issue #8759](https://github.com/agda/agda/issues/8759): Crashes due to missing cases in strict bindings
- [Issue #8767](https://github.com/agda/agda/issues/8767): The strict GHC backend generates slow code
- [Issue #8783](https://github.com/agda/agda/issues/8783): Mimer (C-c C-a) does not automatically use mutually defined functions
- [Issue #8787](https://github.com/agda/agda/issues/8787): Case splitting producing `record` patterns does not omit the implicit fields
- [Issue #8815](https://github.com/agda/agda/issues/8815): Mimer rejects candidate if it generates constraints it would solve in the next step
- [Issue #8828](https://github.com/agda/agda/issues/8828): Meta solutions leak from abstract and opaque blocks
- [Issue #8830](https://github.com/agda/agda/issues/8830): Instance resolution should not ignore available instances
- [Issue #8841](https://github.com/agda/agda/issues/8841): Support Emacs 31
- [Issue #8847](https://github.com/agda/agda/issues/8847): Instance search does not find unquoted definitions in instance blocks
- [Issue #8875](https://github.com/agda/agda/issues/8875): Warn if one includes several version of the same library

Pull requests merged for 2.9.0
------------------------------

- [PR #6911](https://github.com/agda/agda/issues/6911): Reopen PR "Add `record where` syntax sugar (#6603)"
- [PR #7861](https://github.com/agda/agda/issues/7861): Implement a --cubical=no-glue option
- [PR #7877](https://github.com/agda/agda/issues/7877): `record where`, again, again (again?)
- [PR #7881](https://github.com/agda/agda/issues/7881): [ fix #7876 ] Check meta instantiation in constraintMetas
- [PR #7908](https://github.com/agda/agda/issues/7908): Drop GHC 9.0 and below and bump dependencies to LTS 20.26
- [PR #7909](https://github.com/agda/agda/issues/7909): Fix #7906: use compiled clause reducer in termination checker
- [PR #7922](https://github.com/agda/agda/issues/7922): Mimer refactor
- [PR #7951](https://github.com/agda/agda/issues/7951): Improve module checkpointing performance
- [PR #7974](https://github.com/agda/agda/issues/7974): [workflows] run agda after building it (cabal & stack)
- [PR #7985](https://github.com/agda/agda/issues/7985): Fix #7976: warning on REWRITE pragmas when --rewriting is off
- [PR #7986](https://github.com/agda/agda/issues/7986): New option --ghc-trace to instrument code with call trace
- [PR #7990](https://github.com/agda/agda/issues/7990): Modalities in aliases and let-bindings
- [PR #7995](https://github.com/agda/agda/issues/7995): Fix #7994: warn about @tactic attributes ignored in declarations
- [PR #8000](https://github.com/agda/agda/issues/8000): Fix #7998: `instance` silently dropped in `primitive`/`variable` blocks
- [PR #8003](https://github.com/agda/agda/issues/8003): hotfix: support 'record where' in contexts
- [PR #8004](https://github.com/agda/agda/issues/8004): Re #7954: disallow postfix projections in parentheses
- [PR #8008](https://github.com/agda/agda/issues/8008): flake: fix overlay
- [PR #8009](https://github.com/agda/agda/issues/8009): New option --print-options and --bash-complete
- [PR #8014](https://github.com/agda/agda/issues/8014): doc: use the correct format for short options
- [PR #8017](https://github.com/agda/agda/issues/8017): nix: fix build on aarch64-darwin
- [PR #8020](https://github.com/agda/agda/issues/8020): record where: Fix impossible with named module copy
- [PR #8022](https://github.com/agda/agda/issues/8022): fixup: eta for cubical primitives against neutrals
- [PR #8025](https://github.com/agda/agda/issues/8025): Re #1499 #5277 better formatting for error AmbiguousFunClauses
- [PR #8027](https://github.com/agda/agda/issues/8027): Fix #5524: report (with range) duplicate name in fixity declaration
- [PR #8028](https://github.com/agda/agda/issues/8028): [ opt ] Optimize free variable sets
- [PR #8029](https://github.com/agda/agda/issues/8029): Benchmarking and profiling for module application
- [PR #8030](https://github.com/agda/agda/issues/8030): fixup: range of InlineNoExactSplit warning
- [PR #8038](https://github.com/agda/agda/issues/8038): Only generate copies for used names
- [PR #8040](https://github.com/agda/agda/issues/8040): Fix #8033: color warnings by keeping Doc over rendering to String
- [PR #8041](https://github.com/agda/agda/issues/8041): deepseq-1.5.2.0 no longer derives NFData with embedded functions
- [PR #8044](https://github.com/agda/agda/issues/8044): Hyperlink warning names on OSC 8 terminals
- [PR #8047](https://github.com/agda/agda/issues/8047): Highlighting in Emacs Agda information buffer
- [PR #8049](https://github.com/agda/agda/issues/8049): Fix #8048 by generating lock constraints also for implicit arguments
- [PR #8050](https://github.com/agda/agda/issues/8050): MAlonzo: avoid emitting duplicate import statements
- [PR #8052](https://github.com/agda/agda/issues/8052): Re #8024: alert user that --build-library does not accept backends
- [PR #8055](https://github.com/agda/agda/issues/8055): Fix issue #7001: no longer infer lambdas that have no erasure status on their arguments
- [PR #8056](https://github.com/agda/agda/issues/8056): Fix #6939: warn when parser drops misplaced tactic in `Fun`
- [PR #8057](https://github.com/agda/agda/issues/8057): Emacs mode: clean `agda2-forget-all-goals`
- [PR #8058](https://github.com/agda/agda/issues/8058): Structured output of `--help`: options sorted into topics
- [PR #8063](https://github.com/agda/agda/issues/8063): fixup: caching with copy trimming
- [PR #8065](https://github.com/agda/agda/issues/8065): Medium-sized serialization optimizations
- [PR #8069](https://github.com/agda/agda/issues/8069): Bubble transpSysTel' failures upwards
- [PR #8071](https://github.com/agda/agda/issues/8071): Go-to-definition in information buffer
- [PR #8073](https://github.com/agda/agda/issues/8073): globally cache small Term variables
- [PR #8079](https://github.com/agda/agda/issues/8079): Fix operator parsing asymptotics
- [PR #8081](https://github.com/agda/agda/issues/8081): [ fix #8078 ] Fix documentation for piSort
- [PR #8084](https://github.com/agda/agda/issues/8084): Inverse scope optimization
- [PR #8085](https://github.com/agda/agda/issues/8085): containers 0.8
- [PR #8089](https://github.com/agda/agda/issues/8089): Simplify "Installation" documentation
- [PR #8093](https://github.com/agda/agda/issues/8093): [ fix #8092 ] Preserve compiler pragmas when overwriting a definition
- [PR #8095](https://github.com/agda/agda/issues/8095): Fix #8094: run getInteractor after executing `--help` (regression in 2.8.0)
- [PR #8099](https://github.com/agda/agda/issues/8099): Fix #8098: don't delete readonly .agdai files
- [PR #8101](https://github.com/agda/agda/issues/8101): [ fix #8096 ] Redo implementation of LevelUniv infrastructure
- [PR #8102](https://github.com/agda/agda/issues/8102):  Normalization level for Cmd_constraints (C-c C-=)
- [PR #8104](https://github.com/agda/agda/issues/8104): Fix #8103 by removing the parsing hack in BasicOps.metaHelperType
- [PR #8107](https://github.com/agda/agda/issues/8107): Fix #2410: only reduce NON_TERMINATING functions with C-u prefix to C-c C-n
- [PR #8108](https://github.com/agda/agda/issues/8108): Fix #8105: highlight thing shadowed by a clashing definition
- [PR #8110](https://github.com/agda/agda/issues/8110): Remove unnecessary LHS.Unify.LeftInverse computation
- [PR #8115](https://github.com/agda/agda/issues/8115): Implement `{Char, Nat}` primitives for JS backend and add related tests
- [PR #8121](https://github.com/agda/agda/issues/8121): Fix #8119: Dotted expression not impossible
- [PR #8127](https://github.com/agda/agda/issues/8127): Fix #8126: don't error-report generalized variables as projections
- [PR #8129](https://github.com/agda/agda/issues/8129): Fix #8128: point to previous definition in DuplicateDefinition error
- [PR #8135](https://github.com/agda/agda/issues/8135): Fix #8132 by adding SourceFile to SolvedButOpenHoles error
- [PR #8137](https://github.com/agda/agda/issues/8137): Fix #7941: allow splitting on a refined variable
- [PR #8141](https://github.com/agda/agda/issues/8141): Fix for issue #8097
- [PR #8146](https://github.com/agda/agda/issues/8146): Fix #8144: NoSuchModule X gives hint if there is a data/record X
- [PR #8147](https://github.com/agda/agda/issues/8147): Fix #4271: print filenames with modules in errors
- [PR #8149](https://github.com/agda/agda/issues/8149): Print lineage (`WhyInScope`) in `ClashingDefinition` error
- [PR #8151](https://github.com/agda/agda/issues/8151): Add Datatypes of Datatypes to tutorial list
- [PR #8155](https://github.com/agda/agda/issues/8155): Serialize Range in WhyInScope for lineage
- [PR #8156](https://github.com/agda/agda/issues/8156): Fix #8139: tolerate catch-all copatterns
- [PR #8158](https://github.com/agda/agda/issues/8158): Fix #7646 by synching goal command range with interaction range
- [PR #8159](https://github.com/agda/agda/issues/8159): Fix issue #5791: list all possible file extensions in FileNotFound error
- [PR #8160](https://github.com/agda/agda/issues/8160): Re #7225: remove some GenericDocErrors
- [PR #8162](https://github.com/agda/agda/issues/8162): Rename GenericDocErrors in Generalize.hs
- [PR #8169](https://github.com/agda/agda/issues/8169): Fix #8168 by catching ParseErrors in expressions Mimer produces
- [PR #8173](https://github.com/agda/agda/issues/8173): Do not set default input method to "Agda" globally
- [PR #8174](https://github.com/agda/agda/issues/8174): Add .agdai files to 'completion-ignored-extensions'
- [PR #8175](https://github.com/agda/agda/issues/8175): Remove usages of deprecated 'window-system' variable
- [PR #8176](https://github.com/agda/agda/issues/8176): Add custom setter to 'agda2-mode-abbrevs-use-defaults'
- [PR #8177](https://github.com/agda/agda/issues/8177): Allow disabling resizing of minibuffer due to input method
- [PR #8178](https://github.com/agda/agda/issues/8178): Check responses of commands issued by Agda to Emacs
- [PR #8179](https://github.com/agda/agda/issues/8179): Add support for 'repeat-mode'
- [PR #8181](https://github.com/agda/agda/issues/8181): Xref support for Agda2-mode
- [PR #8184](https://github.com/agda/agda/issues/8184): Reinterpret --termination-depth as max depth and do iterative deepening
- [PR #8194](https://github.com/agda/agda/issues/8194): UselessImport warning instead of ParseError for `import M x y`
- [PR #8195](https://github.com/agda/agda/issues/8195): Close #7225: remove Generic[Doc]Error for good
- [PR #8198](https://github.com/agda/agda/issues/8198): PR #8194 ctd.: move desugaring of `open import M args` into scope checker
- [PR #8200](https://github.com/agda/agda/issues/8200): Fix #8197: correct Range for "refine"
- [PR #8204](https://github.com/agda/agda/issues/8204): Fix #3123: instantiation of projection-like functions
- [PR #8205](https://github.com/agda/agda/issues/8205): Running Agda on WASM (resolving merge conflicts of #7561)
- [PR #8207](https://github.com/agda/agda/issues/8207): Fix #8206; refactor scope checker for RecDef a bit
- [PR #8210](https://github.com/agda/agda/issues/8210): Fix #8037 by copying record type along with its projection in module app
- [PR #8217](https://github.com/agda/agda/issues/8217): App range fix for operator application
- [PR #8220](https://github.com/agda/agda/issues/8220): Fix #8218: Update signature for imported rewrite rules
- [PR #8221](https://github.com/agda/agda/issues/8221): Treeless: don't mix up pipelines (#7691)
- [PR #8222](https://github.com/agda/agda/issues/8222): Optimize rewrite rule matching
- [PR #8226](https://github.com/agda/agda/issues/8226): New warning UnusedImports
- [PR #8232](https://github.com/agda/agda/issues/8232): Fix 8228: Parse Error with Display Pragma and Mixfix Operator
- [PR #8234](https://github.com/agda/agda/issues/8234): Fix #8231: Check relevance in `PTerm` matching
- [PR #8235](https://github.com/agda/agda/issues/8235): new feature: quote metas
- [PR #8238](https://github.com/agda/agda/issues/8238): New Warning to Fix #5929
- [PR #8239](https://github.com/agda/agda/issues/8239): [ fix #5315 ] Compile erased types to () in the GHC backend
- [PR #8243](https://github.com/agda/agda/issues/8243): [ fix #2691 ] Add basic documentation for simplification
- [PR #8250](https://github.com/agda/agda/issues/8250): Add --literate-markdown-only-agda-blocks option
- [PR #8267](https://github.com/agda/agda/issues/8267): Fix #8263: turn `__IMPOSSIBLE__` into `patternViolation` (regression in 2.6.4)
- [PR #8270](https://github.com/agda/agda/issues/8270): Fix #8269: doc: remove claim that ETA is safe for colists
- [PR #8274](https://github.com/agda/agda/issues/8274): Fix #8273: Consider interface to merge imported whilst checking confluence
- [PR #8278](https://github.com/agda/agda/issues/8278): Improve caching for (large) opaque blocks
- [PR #8279](https://github.com/agda/agda/issues/8279): Library management: support `defaults-X.Y.Z` files
- [PR #8280](https://github.com/agda/agda/issues/8280): Qualified `do` and qualified idiom brackets
- [PR #8292](https://github.com/agda/agda/issues/8292): Separately benchmark Polarity from Positivity; restore forcing of argOccurrences
- [PR #8293](https://github.com/agda/agda/issues/8293): Fix #3677: print names clashing with operators when parsing failed
- [PR #8295](https://github.com/agda/agda/issues/8295): Made it possible to turn off the occurrence analysis for functions
- [PR #8297](https://github.com/agda/agda/issues/8297): Doc on polarities: Cite the associated abstract.
- [PR #8303](https://github.com/agda/agda/issues/8303): GHC 9.14 compatibility
- [PR #8306](https://github.com/agda/agda/issues/8306): Re #8161: Split GeneralizePrepruneError into its three variants
- [PR #8309](https://github.com/agda/agda/issues/8309): Turn off colored terminal output when `NO_COLOR` is set.
- [PR #8310](https://github.com/agda/agda/issues/8310): Fix #8300: appViewM produces correct hiding for postfix projection
- [PR #8313](https://github.com/agda/agda/issues/8313): nix: bump nixpkgs
- [PR #8314](https://github.com/agda/agda/issues/8314): doc/user-manual: render maths as SVG instead of PNG
- [PR #8315](https://github.com/agda/agda/issues/8315): Reify an amount of backtrace when conversion checking fails
- [PR #8317](https://github.com/agda/agda/issues/8317): fix #8242: don't copy records to within themselves
- [PR #8318](https://github.com/agda/agda/issues/8318): #5833: make `with … in` generalise over `refl`
- [PR #8328](https://github.com/agda/agda/issues/8328): Fix #8327: check early for record constructor in let-pattern
- [PR #8329](https://github.com/agda/agda/issues/8329): Fix #8325 by changing an `__IMPOSSIBLE__` to a `fail` (regression in 2.8.0)
- [PR #8330](https://github.com/agda/agda/issues/8330): Fix #8326: handle the implication two-level <= cubical in isTwoLevelEnabled
- [PR #8332](https://github.com/agda/agda/issues/8332): Type check in parallel
- [PR #8333](https://github.com/agda/agda/issues/8333): Add link to "Let's play Agda" to user manual
- [PR #8338](https://github.com/agda/agda/issues/8338): #8337: Look for instance fields in eta records under binders
- [PR #8340](https://github.com/agda/agda/issues/8340): don't allow postulates in --safe lets
- [PR #8342](https://github.com/agda/agda/issues/8342): fix #8215: reduce candidate in its own state
- [PR #8345](https://github.com/agda/agda/issues/8345): Fix #8344: remember whether a LetBinding came from a LetAxiom
- [PR #8348](https://github.com/agda/agda/issues/8348): Erased levels [cubical]
- [PR #8353](https://github.com/agda/agda/issues/8353): Fix #8352: explicitly list JS primitives that should compile to Undefined
- [PR #8364](https://github.com/agda/agda/issues/8364): Support `@tactic` Module Parameters
- [PR #8369](https://github.com/agda/agda/issues/8369): Fix #8365: reduce in wrong context
- [PR #8376](https://github.com/agda/agda/issues/8376):  Fix #7139: LeftInverse: reorder context in Solution steps
- [PR #8378](https://github.com/agda/agda/issues/8378): nix: enable cluster counting
- [PR #8381](https://github.com/agda/agda/issues/8381): Fix #8380: move line comment rule above block comment rule in lexer
- [PR #8382](https://github.com/agda/agda/issues/8382): Stop eta-expanding module applications
- [PR #8383](https://github.com/agda/agda/issues/8383): Free variable computation optimization
- [PR #8392](https://github.com/agda/agda/issues/8392): Progress reporting when checking in parallel
- [PR #8394](https://github.com/agda/agda/issues/8394): Fix --help claiming --type-in-type is the default
- [PR #8397](https://github.com/agda/agda/issues/8397): Make UnknownNamesIn{FixityDecl,PolarityPragmas} error warnings
- [PR #8401](https://github.com/agda/agda/issues/8401): Fix #8400 by remembering the range of the instance keyword
- [PR #8405](https://github.com/agda/agda/issues/8405): [ fix #8393 ] Normalise codomain of piSort when needed
- [PR #8406](https://github.com/agda/agda/issues/8406): Fix #8402: missing OtherAspects in agda.sty
- [PR #8407](https://github.com/agda/agda/issues/8407): JSONTop: avoid needless parentheses around types
- [PR #8409](https://github.com/agda/agda/issues/8409): Adding Sharp modality
- [PR #8410](https://github.com/agda/agda/issues/8410): Fix #7988: smarter figureOutTopLevelModule, prioritizes qualified module
- [PR #8413](https://github.com/agda/agda/issues/8413): Fix #5618: better wording of UselessInstance warning
- [PR #8414](https://github.com/agda/agda/issues/8414): Fix #5839 by adding conPartNotations to the OperatorInformation
- [PR #8416](https://github.com/agda/agda/issues/8416): Retain lineage (`AbstractName`) in `AmbiguousQName` for error reporting
- [PR #8433](https://github.com/agda/agda/issues/8433): Fix #3355: NO_POSITIVITY_CHECK pragmas in where and record
- [PR #8437](https://github.com/agda/agda/issues/8437): Fix #8435 by new warning DeclarationBeforeDefinition
- [PR #8438](https://github.com/agda/agda/issues/8438): Fix #4150 by sorting lone definitions up in a `mutual` block
- [PR #8439](https://github.com/agda/agda/issues/8439): Fix #6173 by inserting missing checkModuleName
- [PR #8444](https://github.com/agda/agda/issues/8444): fixup: traverse telescope properly in checkFibrantSplit
- [PR #8445](https://github.com/agda/agda/issues/8445): Remove transitive closure from positivity checking
- [PR #8447](https://github.com/agda/agda/issues/8447): Deprecate non-ES6 JS module styles
- [PR #8450](https://github.com/agda/agda/issues/8450): Mark all non-delimiter characters as word constituents in `agda2-mode-syntax-table`
- [PR #8451](https://github.com/agda/agda/issues/8451): [ #8283 ] Fix highlighting race condition in agda2-mode
- [PR #8458](https://github.com/agda/agda/issues/8458): [ #8452 ] Make agda2-maybe-goto jump across files
- [PR #8460](https://github.com/agda/agda/issues/8460): re. #8457: only ask if meta is an IP if cubical
- [PR #8462](https://github.com/agda/agda/issues/8462): Fix #8454
- [PR #8463](https://github.com/agda/agda/issues/8463): New `primRewriteNoMatch` primitive for controlling rewrite rule matching
- [PR #8466](https://github.com/agda/agda/issues/8466): Fix #8564: take definition site into account when serializing (Q)Name
- [PR #8469](https://github.com/agda/agda/issues/8469): Bump TeX-Live/setup-texlive-action from 3 to 4
- [PR #8471](https://github.com/agda/agda/issues/8471): Reverted two commits that made certain level arguments erased
- [PR #8473](https://github.com/agda/agda/issues/8473): Make Agda go faster
- [PR #8486](https://github.com/agda/agda/issues/8486): [ fix #7964 ] Properly handle projection-likeness in Mimer
- [PR #8488](https://github.com/agda/agda/issues/8488): Fix #8453: check field types of BUILTIN SIGMA
- [PR #8491](https://github.com/agda/agda/issues/8491): Add lines-per-second information to --profile=modules
- [PR #8498](https://github.com/agda/agda/issues/8498): [ emacs ] Overhaul goal lexer in agda2-goals-action
- [PR #8501](https://github.com/agda/agda/issues/8501): Bump GHC 9.12.2 to 9.12.4
- [PR #8502](https://github.com/agda/agda/issues/8502): Highlighting and go-to-definition in the debug buffer
- [PR #8503](https://github.com/agda/agda/issues/8503): Restrict pattern matching in binding position to eta-equality records (#6845 reopened)
- [PR #8506](https://github.com/agda/agda/issues/8506): [ emacs ] Only jump to an error in the selected window
- [PR #8508](https://github.com/agda/agda/issues/8508): User-manual: versionadded info for warnings
- [PR #8509](https://github.com/agda/agda/issues/8509): Dependencies: allow pqueue-1.7
- [PR #8512](https://github.com/agda/agda/issues/8512): Docs: why is --injective-type-constructors anti-classical & anti-univalent
- [PR #8515](https://github.com/agda/agda/issues/8515): `stripWithClausePatterns` in the right context
- [PR #8518](https://github.com/agda/agda/issues/8518): Serialize fewer generalization records
- [PR #8520](https://github.com/agda/agda/issues/8520): Update context in checkIApplyConfluence
- [PR #8522](https://github.com/agda/agda/issues/8522): Fix #8521 by remembering PossiblyProjectionPattern in DotP parsing
- [PR #8523](https://github.com/agda/agda/issues/8523): Remove inaccurate claim in two-level.lagda.rst
- [PR #8527](https://github.com/agda/agda/issues/8527): Update inaccurate Agda example in record-types.lagda.rst
- [PR #8528](https://github.com/agda/agda/issues/8528): [ emacs ] Fix goal detection in pattern lambdas
- [PR #8530](https://github.com/agda/agda/issues/8530): Fix #8529
- [PR #8533](https://github.com/agda/agda/issues/8533): No longer infer eta for records
- [PR #8541](https://github.com/agda/agda/issues/8541): Fix #6670 #5411 #6240 generalizeTel with open
- [PR #8542](https://github.com/agda/agda/issues/8542): Fix #7629 by correction countPatternVars for HITs
- [PR #8547](https://github.com/agda/agda/issues/8547): Fix #2877: doc: literal overloading is not allowed in patterns
- [PR #8555](https://github.com/agda/agda/issues/8555): Add mathematical bold fraktur to agda-input
- [PR #8556](https://github.com/agda/agda/issues/8556): Fix #4228: also prune genTel from solved interaction metas
- [PR #8560](https://github.com/agda/agda/issues/8560): Fix #3054 by introducing MatchPrio for constructor patterns (regression in 2.6.0)
- [PR #8567](https://github.com/agda/agda/issues/8567): Simplify fix of #6770: remove section updating
- [PR #8569](https://github.com/agda/agda/issues/8569): Fix occurrences in over-applied args, primitives and postulates
- [PR #8575](https://github.com/agda/agda/issues/8575): Add flag for irrelevance
- [PR #8576](https://github.com/agda/agda/issues/8576): [ fix #8557 ] Only resurrect irrelevant variables once
- [PR #8578](https://github.com/agda/agda/issues/8578): Fix #8577: Normalise under varTel in Unify.hs
- [PR #8584](https://github.com/agda/agda/issues/8584): Fix #8583: (Co)InfectiveError: report imported module with range
- [PR #8585](https://github.com/agda/agda/issues/8585): Fix #8580: internal error with _ in pattern synonym definition
- [PR #8588](https://github.com/agda/agda/issues/8588): [ re #8552 ] Add workaround to the release notes + test suite
- [PR #8593](https://github.com/agda/agda/issues/8593): Added `--erased-funext`, `--erased-propext` and `--erased-quotients`
- [PR #8594](https://github.com/agda/agda/issues/8594): Added a missing option to a list in the documentation
- [PR #8601](https://github.com/agda/agda/issues/8601): Fix #8596: termination checker respects copatterns
- [PR #8602](https://github.com/agda/agda/issues/8602): Fix #1680: Stratify termination masks by copattern
- [PR #8604](https://github.com/agda/agda/issues/8604): Bump actions/checkout from 6 to 7
- [PR #8606](https://github.com/agda/agda/issues/8606): Bump actions/cache from 5 to 6
- [PR #8612](https://github.com/agda/agda/issues/8612): Fix #8610
- [PR #8615](https://github.com/agda/agda/issues/8615): Fix #8587
- [PR #8617](https://github.com/agda/agda/issues/8617): Place -WShouldBeEtaRecordPattern under --exact-split.
- [PR #8628](https://github.com/agda/agda/issues/8628): Fixes #8626: treat lazy split pattern as dot pattern when there is nothing left to split in `compile`
- [PR #8632](https://github.com/agda/agda/issues/8632): Remove case-of-case optimization in compiler
- [PR #8635](https://github.com/agda/agda/issues/8635): Repair `nix build`
- [PR #8637](https://github.com/agda/agda/issues/8637): Bump actions/setup-python from 6 to 7
- [PR #8640](https://github.com/agda/agda/issues/8640): Allow aeson-2.3
- [PR #8643](https://github.com/agda/agda/issues/8643): Allow deepseq-1.5.2.0 (warns about rnf for functions)
- [PR #8646](https://github.com/agda/agda/issues/8646): Fix `COMPILE JS _∷_`
- [PR #8648](https://github.com/agda/agda/issues/8648): Fix #8647: for the sake of caching handle FOREIGN pragmas in the tc
- [PR #8652](https://github.com/agda/agda/issues/8652): Fix for #8636
- [PR #8657](https://github.com/agda/agda/issues/8657): [ fix #8649 ] Don't eta-expand no-eta records in confluence checker
- [PR #8658](https://github.com/agda/agda/issues/8658): Fix #8634: internal error with --interaction when .agda-lib file contains bogus fields
- [PR #8661](https://github.com/agda/agda/issues/8661): Upstream emacs mode fixes
- [PR #8662](https://github.com/agda/agda/issues/8662): Highlight ShouldBeEtaRecordPattern the same way as exactSplitWarnings
- [PR #8663](https://github.com/agda/agda/issues/8663): [wasm] nix: Bump nix pkgs for ghc-wasm to include critical bug fix for ghc/ghc#27447
- [PR #8667](https://github.com/agda/agda/issues/8667): Add missing flags to builtin modules
- [PR #8669](https://github.com/agda/agda/issues/8669): Fix #8638
- [PR #8671](https://github.com/agda/agda/issues/8671): Fix #8627: make --build-library on builtin library work
- [PR #8675](https://github.com/agda/agda/issues/8675): Dead code elimination: don't traverse meta judgement types
- [PR #8677](https://github.com/agda/agda/issues/8677): Fix #8599: classifyPattern: projection patterns only in LHSs
- [PR #8678](https://github.com/agda/agda/issues/8678): [ fix #5665 ] Close information gaps in the JSON interaction protocol
- [PR #8679](https://github.com/agda/agda/issues/8679): Fix #7564: Do not crash when trying eta-contraction on over-applied constructor.
- [PR #8681](https://github.com/agda/agda/issues/8681): Change R.constructor so that R is the record module rather than the type
- [PR #8682](https://github.com/agda/agda/issues/8682): Fix #8680 (pattern syn) by removing spurious `__IMPOSSIBLE__`
- [PR #8685](https://github.com/agda/agda/issues/8685): Fix #8683: check cubical side conditions also in inference mode
- [PR #8690](https://github.com/agda/agda/issues/8690): Fix #8686: False via projection-like due to non-injective type of principal argument
- [PR #8691](https://github.com/agda/agda/issues/8691): Fix #8688: positivity checker now also descends into Sort
- [PR #8701](https://github.com/agda/agda/issues/8701): Alternative fix of #8687
- [PR #8702](https://github.com/agda/agda/issues/8702): [ fix #8694 ] Take relevance into account for cycle rule in LHS unifier
- [PR #8706](https://github.com/agda/agda/issues/8706): Fix for #8700
- [PR #8707](https://github.com/agda/agda/issues/8707): Fix #8699 by masking irrelevant/Prop-sorted subterms in dot patterns in the termination checker
- [PR #8708](https://github.com/agda/agda/issues/8708): Fix #8697 by indexing the memo map for Double by their Word64 representation
- [PR #8709](https://github.com/agda/agda/issues/8709): Fix #8696 by eta-expanding data/recClauses before positivity checking
- [PR #8711](https://github.com/agda/agda/issues/8711): [ fix #8710 ] merge builtin rewrites when adding import
- [PR #8719](https://github.com/agda/agda/issues/8719): Small bugfix for Cubical Glue/HCompU (fixes #6198)
- [PR #8720](https://github.com/agda/agda/issues/8720): Compile constructors to string-tagged JS arrays
- [PR #8723](https://github.com/agda/agda/issues/8723): Add Agda Web to the manual
- [PR #8729](https://github.com/agda/agda/issues/8729): Fix #8532 by ensuring projectTyped gets a reduced type in antiUnify (regression in 2.5.3)
- [PR #8732](https://github.com/agda/agda/issues/8732): Fix #8698 by disallowing named where modules under with
- [PR #8736](https://github.com/agda/agda/issues/8736): [ #8591 ] Added a test case
- [PR #8738](https://github.com/agda/agda/issues/8738): Fix #1438: new warning FixityDeclarationForNonOperator
- [PR #8740](https://github.com/agda/agda/issues/8740): Fix issue 8336 by turning projection-like functions back into Defs (regression in 2.6.4)
- [PR #8743](https://github.com/agda/agda/issues/8743): Tried to fix a bug related to PR #8593
- [PR #8745](https://github.com/agda/agda/issues/8745): Support for `[]-cong`
- [PR #8768](https://github.com/agda/agda/issues/8768): Strict lets
- [PR #8770](https://github.com/agda/agda/issues/8770): Build with GHC 10.0.0
- [PR #8772](https://github.com/agda/agda/issues/8772): Fix #8771 by unspining also the transformed term in checkInternal (regression in 2.6.4)
- [PR #8774](https://github.com/agda/agda/issues/8774): Fix #8545 by storing data/recClause as just Term
- [PR #8778](https://github.com/agda/agda/issues/8778): Fix #8777: replace call to canonicalName by reduce
- [PR #8779](https://github.com/agda/agda/issues/8779): Fix #7664 checkParameters (revisit #8722)
- [PR #8789](https://github.com/agda/agda/issues/8789): Fix issue #8788
- [PR #8790](https://github.com/agda/agda/issues/8790): [ fix #8703 ] Treat underapplied functions as stuck
- [PR #8791](https://github.com/agda/agda/issues/8791): Fix #8787: drop hidden fields in record pattern when introduced by case-split
- [PR #8800](https://github.com/agda/agda/issues/8800): agda-mode: Rebind mouse-2 to 'agda2-goto-definition-mouse'
- [PR #8802](https://github.com/agda/agda/issues/8802): Makefile: new goal `fast-forward-ecosystem`; update submodules [ecosystem]
- [PR #8804](https://github.com/agda/agda/issues/8804): Fix #8783: Mimer: use functions from mutual block as default hints
- [PR #8806](https://github.com/agda/agda/issues/8806): Fix #8171 by creating metas at the unitPolarity (@++)
- [PR #8810](https://github.com/agda/agda/issues/8810): Fix #8808 by removing shortcut creating unbound de Bruijn indices
- [PR #8812](https://github.com/agda/agda/issues/8812): Fix #8811 by relaxing the modallity in the occurs check of sort annotations
- [PR #8816](https://github.com/agda/agda/issues/8816): Fix #8815 and #7972 by postponing constraints in Mimer
- [PR #8817](https://github.com/agda/agda/issues/8817): [ fix #8695 ] Treat occurrences in constructors of HITs as weakly rigid
- [PR #8822](https://github.com/agda/agda/issues/8822): Safer fix of #7181 (regression in 2.7.0)
- [PR #8833](https://github.com/agda/agda/issues/8833): [ fix #8765 ] Add separate response for errors in other files
- [PR #8837](https://github.com/agda/agda/issues/8837): [ fix #8828 ] Don't solve metas from outside current abstract block
- [PR #8840](https://github.com/agda/agda/issues/8840): [ #8839 ] Improved the detection of error/warning locations
- [PR #8843](https://github.com/agda/agda/issues/8843): Fix #8834 by checking cohesion and polarity when abstracting telescopes
- [PR #8850](https://github.com/agda/agda/issues/8850): Fix #8847 by not propagating `instance` to `unquoteDecl`s
- [PR #8852](https://github.com/agda/agda/issues/8852): Fix #8851: check that unquoteDecl invocation actually defines names
- [PR #8856](https://github.com/agda/agda/issues/8856): Fix #8853 by adding a case for `IApply` to `reconstructParameters`
- [PR #8869](https://github.com/agda/agda/issues/8869): Fix #8739: wrong implicit argument in LHS: also mention possible args
- [PR #8870](https://github.com/agda/agda/issues/8870): Decide whether pi is large based on original codomain sort
- [PR #8876](https://github.com/agda/agda/issues/8876): Fix #8875: warning to show dependency version conflicts

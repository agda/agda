Release notes for Agda version 2.6.4
====================================

Installation
------------

* Removed the cabal flag `cpphs` that enabled building Agda with `cpphs` instead of the default C preprocessor.

Pragmas and options
-------------------

* New command-line option `--numeric-version` to just print the version number of Agda.

* Option `--version` now also prints the cabal flags active in this build of Agda
  (e.g. whether Agda was built with `-f enable-cluster-counting`).

* New command-line option `--trace-imports` to switch on notification messages
  on the end of compilation of an imported module
  or on access to an interface file during the type-checking.

  See [--trace-imports](https://agda.readthedocs.io/en/v2.6.4/tools/command-line-options.html#cmdoption-trace-imports)
  in the documentation for more.

* New option `--no-infer-absurd-clauses` to simplify coverage checking and case splitting:
  Agda will then no longer attempt to automatically eliminate absurd clauses which can be a costly operation.
  This means that these absurd clauses have to be written out in the Agda text.
  Try this option if you experience type checking performance degradation with omitted absurd clauses.

  Opposite: `--infer-absurd-clauses`.

* Benign warnings are now printed together with their warning name, to give a hint how they can be disabled
  (see [#6229](https://github.com/agda/agda/issues/6229)).

* New option `--level-universe` to make `Level` inhabit its own universe `LevelUniv`:
  When this option is turned on, `Level` can now only depend on terms of type `Level`.

  Note: While compatible with the `--cubical` option, this option is currently not compatible with cubical builtin files, and an error will be raised when trying to import them in a file using `--level-universe`.

  Opposite: `--no-level-universe`.

* Most boolean options now have their opposite, e.g., `--allow-unsolved-metas` is complemented by `--no-allow-unsolved-metas`.
  With the opposite one can override a previously given option.
  Options given on the command line are overwritten by options given in the `.agda-lib` file,
  which in turn get overwritten by options given in the individual `.agda` file.

  New options (all on by default):
  - `--no-allow-exec`
  - `--no-allow-incomplete-matches`
  - `--no-allow-unsolved-metas`
  - `--no-call-by-name`
  - `--no-cohesion`
  - `--no-count-clusters`
  - `--no-erased-matches`
  - `--no-erasure`
  - `--no-experimental-irrelevance`
  - `--no-flat-split`
  - `--no-guarded`
  - `--no-injective-type-constructors`
  - `--no-keep-covering-clauses`
  - `--no-keep-pattern-variables`
  - `--no-omega-in-omega`
  - `--no-postfix-projections`
  - `--no-rewriting`
  - `--no-show-identity-substitutions`
  - `--no-show-implicit`
  - `--no-show-irrelevant`
  - `--no-two-level`
  - `--no-type-in-type`
  - `--eta-equality`
  - `--fast-reduce`
  - `--forcing`
  - `--import-sorts`
  - `--load-primitives`
  - `--main`
  - `--pattern-matching`
  - `--positivity-check`
  - `--print-pattern-synonyms`
  - `--projection-like`
  - `--termination-check`
  - `--unicode`

* Option `--flat-split` again implies `--cohesion`.
  Reverts change introduced in Agda 2.6.3 where `--cohesion` was a prerequisite for `--flat-split`.

* Pragma `INLINE` may now be applied to constructors of types supporting co-pattern matching.
  It enables translation of right-hand-side constructor applications to left-hand-side co-pattern splits (see [PR #6682](https://github.com/agda/agda/pull/6682)).
  For example, this translation allows the `nats` function to pass termination checking:
  ```agda
    record Stream (A : Set) : Set where
      coinductive; constructor _∷_
      field head : A
            tail : Stream A
    open Stream
    {-# INLINE _∷_ #-}

    nats : Nat → Stream Nat
    nats n = n ∷ nats (1 + n)
  ```
  Inlining transforms the definition of `nats` to the following definition by copattern matching:
  ```agda
    nats n .head = n
    nats n .tail = nats (1 + n)
  ```
  This form is accepted by the termination checker;
  unlike the form before inlining, it does not admit any infinite reduction sequences.

  If option `--exact-split` is on, the inlining will trigger a `InlineNoExactSplit` warning for `nats`.
  This warning can be disabled as usual, with `-WnoInlineNoExactSplit`.

* New option `--large-indices`, controlling whether constructors of
  indexed data types are allowed to refer to data that would be "too
  large" to fit in their declared sort. Large indices are disallowed by
  default; see the [language changes](#language) for details.

* New option `--forced-argument-recursion`, on by default, controlling
  whether forced constructor arguments are usable for termination
  checking. This flag may be necessary for Agda to accept nontrivial
  uses of induction-induction.

Library management
------------------

* [**Breaking**] One can no longer have `.agda-lib` files that are
  located below the "project root", on the path to the file that is
  being type-checked (see
  [#6465](https://github.com/agda/agda/issues/6465)).

  For instance, if you have a module called `A.B.C` in the directory
  `Root/A/B`, then an error is raised if there are `.agda-lib` files
  in `Root/A` or `Root/A/B`.

  Previously such `.agda-lib` files were ignored.

Interaction and emacs mode
--------------------------

* Agda now supports reading files with extension `.lagda.typ`, and use the parser for
  markdown files to parse them.
  To edit such files in Emacs with Agda support, one needs to add the line
  ```elisp
  (add-to-list 'auto-mode-alist '("\\.lagda.typ\\'" . agda2-mode))
  ```
  to `.emacs`.

  Generation for highlighted code like HTML is unsupported for Typst.
  One may generate HTML with typst input, but that makes little sense,
  and markdown is recommended instead when HTML export is desired.

* Helper function (`C-c C-h`) does not abstract over module parameters anymore
  (see [#2271](https://github.com/agda/agda/issues/2271))
  and neither over generalized `variable`s
  (see [#6689](https://github.com/agda/agda/pull/6689)).

* New Agda input mode prefix `box` for APL boxed operators, e.g. `\box=` for ⌸;
  see PR [#6510](https://github.com/agda/agda/pull/6510/files) for full list of bindings.

* Cubical Agda will now report boundary information for interaction
  points which are not at the top-level of their respective clauses.
  This includes bodies of `Path`-typed values, the faces of a partial
  element, arguments to functions returning paths, etc.

  Since this information is available in a structured way _during
  interaction_, the "goal type, context, and inferred type" command will
  also display the value of the expression at each relevant face.

  See also [PR #6529](https://github.com/agda/agda/pull/6529) for a
  deeper explanation and a demo video.

Syntax
------

* Agda now skips the UTF8 byte order mark (BOM) at beginning of files
  (see [#6524](https://github.com/agda/agda/issues/6524)).
  Previously, the BOM caused a parse error.

* If the new option `--hidden-argument-puns` is used, then the pattern
  `{x}` is interpreted as `{x = x}`, and the pattern `⦃ x ⦄` is
  interpreted as `⦃ x = x ⦄` (see
  [#6325](https://github.com/agda/agda/issues/6325)). Here `x` must be
  an unqualified name that does not refer to a constructor that is in
  scope: if `x` is qualified, then the pattern is not interpreted as a
  pun, and if `x` is unqualified and refers to a constructor that is
  in scope, then the code is rejected.

  This feature can be turned off using `--no-hidden-argument-puns`.

  Note that `{(x)}` and `⦃ (x) ⦄` are not interpreted as puns.

  Note also that `{x}` is not interpreted as a pun in `λ {x} → …` or
  `syntax f {x} = …`. However, `{x}` is interpreted as a pun in
  `λ (c {x}) → …`.

Language
--------

* [**Breaking**] Constructor arguments are no longer allowed to store
  values of a type larger than their own sort, even when these values
  are forced by the indices of a constructor.

  This fixes a particular instance of the incompatibility between
  structural recursion and impredicativity, which could previously be
  exploited through the use of large data-type indices.
  (see [#6654](https://github.com/agda/agda/issues/6654)).

  This behaviour can be controlled with the flag `--large-indices`. Note
  that, when `--large-indices` is enabled, forced constructor arguments
  should not be used for termination checking. The flag
  `--[no-]forced-argument-recursion` makes the termination checker skip
  these arguments entirely. When `--safe` is given, `--large-indices` is
  incompatible with `--without-K` _and_ incompatible with
  `--forced-argument-recursion`.

* Added [`opaque` definitions](https://agda.readthedocs.io/en/v2.6.4/language/opaque-definitions.html),
  a mechanism for finer-grained control of unfolding. Unlike `abstract`
  definitions, which can never be unfolded outside of (a child module
  of) the defining module, opacity can be toggled at use-sites:

  ```agda
  opaque
    foo : Set
    foo = Nat

  opaque
    unfolding foo

    _ : foo
    _ = 123
  ```

* Unless `--no-import-sorts` is given, `Set` is in scope as before,
  but `Prop` is only in scope when `--prop` is active.
  Additionally `SSet` is now in scope when `--two-level` is active
  (see [#6634](https://github.com/agda/agda/pull/6634)).

* New sorts `Propω`, `Propω₁`, etc., in analogy to `Setω`, `Setω₁` etc.
  Requires option `--prop`.

  Example:
  ```agda
  {-# OPTIONS --prop #-}

  open Agda.Primitive

  variable
    ℓ : Level
    A : Set ℓ

  -- Lists of elements of types at any finite level.

  data HList : Setω where
    []  : HList
    _∷_ : A → HList → HList

  variable
    x  : A
    xs : HList

  -- Predicate stating that all elements satisfy a given property.

  data All (P : {A : Set ℓ} → A → Prop ℓ) : HList → Propω where
    []  : All P []
    _∷_ : P x → All P xs → All P (x ∷ xs)
  ```

* [**Breaking**] The algorithm for resolution of instance arguments
  has been simplified. It will now only rely on the type of instances
  to determine which candidate it should use, and no longer on their
  values.

Erasure
-------

* [**Breaking**] The new flag `--erasure` turns on support for erasure
  ([#6349](https://github.com/agda/agda/issues/6349)).

  This flag is infective.
  It is implied by `--erase-record-parameters` and `--erased-matches`.

  Unless this flag is active the following things are prohibited:
  * Use of the annotations `@0` and `@erased`.
  * Use of names defined in Cubical Agda in Erased Cubical Agda.

  When `--erasure` is used the parameter arguments of constructors and
  projections are marked as erased
  ([#4786](https://github.com/agda/agda/issues/4786)), with one
  exception: for indexed data types this only happens if the
  `--with-K` flag is active
  ([#6297](https://github.com/agda/agda/issues/6297)).

  For instance, the type of the constructor `c` below is `{@0 A :
  Set} → D A`, and the type of the projection `R.f` is `{@0 A : Set}
  → R A → A`:
  ```agda
  {-# OPTIONS --erasure #-}

  data D (A : Set) : Set where
    c : D A

  record R (A : Set) : Set where
    field
      f : A
  ```

* [**Breaking**] Unless the new flag `--erased-matches` is used
  matching is not allowed in erased positions for single-constructor
  data types or record types without η-equality
  ([#6349](https://github.com/agda/agda/issues/6349)).

  This flag is infective and implied by `--with-K`.
  If it is given explicitly, it implies `--erasure`.

* [**Breaking**] Added a hard compile-time mode (see
  [#4743](https://github.com/agda/agda/issues/4743)).

  When the hard compile-time mode is used all definitions are treated
  as erased. The hard compile-time mode is entered when an erased
  definition is checked (including an erased data or record type or
  module), but not when (for instance) a type-signature is checked.

  Previously the following code was rejected:
  ```agda
  open import Agda.Builtin.Bool

  @0 f : @0 Bool → Bool
  f = λ where
    true  → false
    false → true
  ```
  Now this code is accepted (if `--erasure` is used). On the other
  hand, the following code which used to be accepted is now rejected
  (if `--erasure` is used), because the pattern-matching lambda is
  treated as erased:
  ```agda
  open import Agda.Builtin.Equality

  data Unit : Set where
    unit : Unit

  mutual

    f : Unit → Unit
    f = _

    @0 f≡ : f ≡ λ { unit → unit }
    f≡ = refl
  ```

* One can now mark data and record types and modules as erased (see
  [#4743](https://github.com/agda/agda/issues/4743)).

  If a data type is marked as erased, then it can only be used in
  erased settings, and its constructors are erased. A data type is
  marked as erased by writing `@0` or `@erased` right after the `data`
  keyword of the data type's declaration:
  ```agda
  data @0 D₁ : Set where
    c : D₁

  data @0 D₂ : Set

  data D₂ where
    c : D₁ → D₂

  interleaved mutual

    data @0 D₃ : Set where

    data D₃ where
      c : D₃
  ```

  If a record type is marked as erased, then it can only be used in
  erased settings, its constructors and fields are erased, and
  definitions in the record module are erased. A record type is marked
  as erased by writing `@0` or `@erased` right after the `record`
  keyword of the record type's declaration:
  ```agda
  record @0 R₁ : Set where
    field
      x : D₁

  record @0 R₂ : Set

  record R₂ where
    field
      x : R₁
  ```

  If a module is marked as erased, then all definitions inside the
  module (and in the module's telescope) are erased. A module is
  marked as erased by writing `@0` or `@erased` right after the
  `module` keyword:
  ```agda
  module @0 _ where

    F : @0 Set → Set
    F A = A

  module M (A : Set) where

    record R : Set where
      field
        @0 x : A

  module @0 N (@0 A : Set) = M A

  G : (@0 A : Set) → let module @0 M₂ = M A in Set
  G A = M.R B
    module @0 _ where
      B : Set
      B = A
  ```
  If an erased module is defined by a module application, then erased
  names can be used in the application, as in the definition of `N`
  above.

* Equivalence primitives no longer require full `--cubical` mode,
  `--erased-cubical` suffices. Equivalence definition is moved out of
  `Agda.Builtin.Cubical.Glue` into its own module `Agda.Builtin.Cubical.Equiv`,
  the former reexports the latter.

Reflection
----------

* `FOREIGN` and `COMPILE` pragmas can now be generated using two new reflection primitives:

  ```agda
  pragmaForeign : String → String → TC ⊤
  pragmaCompile : String → Name → String → TC ⊤
  ```

* Add 4 reflection primitives of the form `ask*` and `with*`:

  ```agda
  withNormalisation : ∀ {a} {A : Set a} → Bool → TC A → TC A
  askNormalisation  : TC Bool

  withExpandLast : ∀ {a} {A : Set a} → Bool → TC A → TC A
  askExpandLast  : TC Bool

  withReduceDefs : ∀ {a} {A : Set a} → (Σ Bool λ _ → List Name) → TC A → TC A
  askReduceDefs  : TC (Σ Bool λ _ → List Name)

  askReconstructed  : TC Bool
  ```
  to change the behaviour of `inferType`, `checkType`, `quoteTC`, `getContext`.

* [**Breaking**] The type of `withReconstructed` has been changed from

  ```agda
  withReconstructed : ∀ {a} {A : Set a} →        TC A → TC A

  ```
  to
  ```agda
  withReconstructed : ∀ {a} {A : Set a} → Bool → TC A → TC A
  ```
  to match the type of primitives of the form `with*`.

* Two primitives `onlyReduceDefs` and `dontReduceDefs` are removed but re-implemented
  using the new family of primitives `with*` and `ask*` for backward compatibility.

* Blocking the type-checking monad can now be done with more precision
  by using the `Blocker` type, and the `blockTC` primitive:

  ```agda
  data Blocker : Set where
    blockerAny  : List Blocker → Blocker
    blockerAll  : List Blocker → Blocker
    blockerMeta : Meta → Blocker
  ```

  When blocking on a value of this type, the TCM computation will only
  be retried when any (resp. all) of the mentioned metavariables have
  been solved. This can avoid getting into loops where a macro blocks on
  a meta, gets unblocked, traverses some term again, and then blocks on
  a meta that was already present.

  The `blockOnMeta` builtin has been deprecated, and an implementation
  in terms of `blockTC` is given for backwards compatibility.


Other issues closed
-------------------

For 2.6.4, the following issues were also
[closed](https://github.com/agda/agda/issues?q=is%3Aissue+milestone%3A2.6.4+is%3Aclosed)
(see [bug tracker](https://github.com/agda/agda/issues)):

- [#1181](https://github.com/agda/agda/issues/1181): Display of let-bound variables in goals and error messages
- [#3437](https://github.com/agda/agda/issues/3437): Add Propω
- [#3605](https://github.com/agda/agda/issues/3605): Improve constraint reporting for cubical
- [#3690](https://github.com/agda/agda/issues/3690): Cubical interaction: Display inferred type with interval variables instantiated
- [#5900](https://github.com/agda/agda/issues/5900): De Bruijn fail in Cubical (Was: Garbled boundary contexts & naming eta expansion.)
- [#6124](https://github.com/agda/agda/issues/6124): Reflection: cannot reduce type because variable is erased
- [#6140](https://github.com/agda/agda/issues/6140): Unapplied `List` and `Maybe` are sometimes translated to `[AgdaAny]` and `Maybe AgdaAny` by GHC backend
- [#6229](https://github.com/agda/agda/issues/6229): Print warning name along with warning text
- [#6271](https://github.com/agda/agda/issues/6271): Cubical: should generated code corresponding to erased constructors be erased?
- [#6272](https://github.com/agda/agda/issues/6272): Put Level type in a different sort
- [#6309](https://github.com/agda/agda/issues/6309): Drop support for GHC 8.0, 8.2, and 8.4
- [#6325](https://github.com/agda/agda/issues/6325): Hidden argument puns
- [#6333](https://github.com/agda/agda/issues/6333): Misleading file path in "Unrecognised option" error
- [#6336](https://github.com/agda/agda/issues/6336): Paradoxical self-reference in endpoints for path constructors
- [#6364](https://github.com/agda/agda/issues/6364): Instance candidates filtered out by type errors
- [#6371](https://github.com/agda/agda/issues/6371): Preserve metavariable name suggestion when eta-expanding
- [#6374](https://github.com/agda/agda/issues/6374): Refine does not work for overloaded record constructors
- [#6380](https://github.com/agda/agda/issues/6380): Confusing warning about turning instances into instances
- [#6395](https://github.com/agda/agda/issues/6395): `dataXXX` identifiers mis-parsed by {-# COMPILE GHC #-}
- [#6407](https://github.com/agda/agda/issues/6407): Agsy produces clauses with out of scope variables
- [#6413](https://github.com/agda/agda/issues/6413): Miscompilation of nested patterns in erased fields
- [#6415](https://github.com/agda/agda/issues/6415): Apparent infinite loop in cubical with --lossy-unification
- [#6418](https://github.com/agda/agda/issues/6418): Bug in rewriting with cubical primitives
- [#6434](https://github.com/agda/agda/issues/6434): Option to increase performance: do not filter out absurd clauses automatically
- [#6448](https://github.com/agda/agda/issues/6448): Don't define dependencies for elisp files included in the agda2-mode package
- [#6506](https://github.com/agda/agda/issues/6506): Cubical: `with` abstraction failing to type check
- [#6521](https://github.com/agda/agda/issues/6521): Support GHC 9.6 with cabal
- [#6523](https://github.com/agda/agda/issues/6523): Soundness bug: Tick constraints not properly propogated in Guarded Cubical
- [#6524](https://github.com/agda/agda/issues/6524): Ignore Unicode byte order mark
- [#6525](https://github.com/agda/agda/issues/6525): Recent Emacs's escape character handling improvement leads to an error when loading agda-mode
- [#6528](https://github.com/agda/agda/issues/6528): Guarded can block on solved metas
- [#6530](https://github.com/agda/agda/issues/6530): Miscompilation of case split RHS lambdas
- [#6541](https://github.com/agda/agda/issues/6541): Internal error in Agda.TypeChecking.Reduce.Fast
- [#6551](https://github.com/agda/agda/issues/6551): Doc: the keywords `hiding`,`public`, `renaming`, and `using` are always reserved
- [#6573](https://github.com/agda/agda/issues/6573): Check on presence of `--erasure` in `--erase-record-parameters` comes too early
- [#6581](https://github.com/agda/agda/issues/6581): Cubical: no canonicity for record types without η-equality
- [#6605](https://github.com/agda/agda/issues/6605): Doc: comments in "libraries" file
- [#6621](https://github.com/agda/agda/issues/6621): Enable K also for SSetω (like for SSet)
- [#6622](https://github.com/agda/agda/issues/6622): Bad error for `mutual` in implicit mutual block
- [#6624](https://github.com/agda/agda/issues/6624): Suffix not working for SSet
- [#6627](https://github.com/agda/agda/issues/6627): CheckArguments call exposes dummy checkArguments return type
- [#6632](https://github.com/agda/agda/issues/6632): hcompU eta rule in conversion checker loses solution
- [#6633](https://github.com/agda/agda/issues/6633): Bad interaction of Type:Type and SSet
- [#6648](https://github.com/agda/agda/issues/6648): `--level-universe` not respected when solving funSort `_->_ : ? -> Set -> SetOmega`
- [#6651](https://github.com/agda/agda/issues/6651): Agda fails on `univSort ? = SetOmega` even when `SizeUniv` is a solution
- [#6654](https://github.com/agda/agda/issues/6654): Forcing analysis is inconsistent for large indices
- [#6660](https://github.com/agda/agda/issues/6660): `{-# INLINE #-}` for copattern constructors
- [#6662](https://github.com/agda/agda/issues/6662): Error message for unsafe option combinations has wrong pluralization
- [#6677](https://github.com/agda/agda/issues/6677): Helper function type includes generalized parameters
- [#6687](https://github.com/agda/agda/issues/6687): Termination checker bug with CATCHALL
- [#6702](https://github.com/agda/agda/issues/6702): Inlining constructors to copattern should give warning with `--exact-split`
- [#6706](https://github.com/agda/agda/issues/6706): Shape-irrelevant variables marked as irrelevant in human-readable context
- [#6711](https://github.com/agda/agda/issues/6711): IMPOSSIBLE internal error on primStringUncons when no builtin Sigma provided
- [#6714](https://github.com/agda/agda/issues/6714): Compiling Agda HEAD with Emacs 29+ reports docstring error
- [#6715](https://github.com/agda/agda/issues/6715): Type checking loops on certain pattern match in cubical
- [#6720](https://github.com/agda/agda/issues/6720): Cubical: IMPOSSIBLE in Sort.hs during checking with cubical
- [#6725](https://github.com/agda/agda/issues/6725): Cubical: IMPOSSIBLE in Reduce.hs

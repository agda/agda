Release notes for Agda version 2.6.3
====================================

Highlights
----------

* Added support for [Erased Cubical
  Agda](https://agda.readthedocs.io/en/latest/language/cubical.html#cubical-agda-with-erased-glue),
  a variant of Cubical Agda that is supported by the GHC backend,
  under the flag `--erased-cubical`.

* Added a new flag `--cubical-compatible` to turn on generation of
  Cubical Agda-specific support code (previously this behaviour was
  part of `--without-K`).

  Since `--cubical-compatible` mode implies that functions should work
  with the preliminary support for [indexed inductive types in Cubical
  Agda](https://agda.readthedocs.io/en/latest/language/cubical.html#indexed-inductive-types),
  many pattern matching functions will now emit an
  `UnsupportedIndexedMatch` warning, indicating that the function will
  not compute when applied to transports (from `--cubical` code).

  This warning can be disabled with `-WnoUnsupportedIndexedMatch`, which
  can be used either in an `OPTIONS` pragma or in your `agda-lib` file.
  The latter is recommended if your project is only
  `--cubical-compatible`, or if it is already making extensive use of
  indexed types.

* New primitives `declareData`, `defineData`, and `unquoteDecl data`
  for generating new data types have been added to the [reflection
  API](https://agda.readthedocs.io/en/latest/language/reflection.html#metaprogramming).

* Thanks to a number of performance improvements, Agda 2.6.3 is about
  30% faster than Agda 2.6.2.2 at type-checking the standard library
  with the `--without-K` flag, and 10% faster when using with the
  (new) `--cubical-compatible` flag instead (some details can be found
  [here](https://github.com/agda/agda/issues/6049#issuecomment-1293698980)).

Installation and infrastructure
-------------------------------

Agda supports GHC versions 8.0.2 to 9.4.3.

Erasure
-------

* The new option `--erased-cubical` turns on a variant of Cubical Agda
  (see [#4701](https://github.com/agda/agda/issues/4701)).

  When this variant of Cubical Agda is used glue (and some related
  builtins) may only be used in erased settings. One can import
  regular Cubical Agda code from this variant of Cubical Agda, but
  names defined using Cubical Agda are (mostly) treated as if they had
  been marked as erased. See the [reference
  manual](https://agda.readthedocs.io/en/latest/language/cubical.html#cubical-agda-with-erased-glue-and-erased-higher-constructors)
  for more details.

  The GHC backend can compile code that uses `--erased-cubical` if the
  top-level module uses this flag.

  This feature is experimental.

* The parameter arguments of constructors and record fields are now
  marked as erased
  ([#4786](https://github.com/agda/agda/issues/4786)), with one
  exception: for indexed data types this only happens if the
  `--with-K` flag is active
  ([#6297](https://github.com/agda/agda/issues/6297)).

  For instance, the type of the constructor `c` below is now `{@0 A :
  Set} → D A`, and the type of the record field `R.f` is `{@0 A : Set}
  → R A → A`:
  ```agda
  data D (A : Set) : Set where
    c : D A

  record R (A : Set) : Set where
    field
      f : A
  ```

* Added an option `--erase-record-parameters` that additionally marks
  parameters to definitions in a record module as erased
  ([#5770](https://github.com/agda/agda/issues/5770)). For example:

  ```agda
  {-# OPTIONS --erase-record-parameters #-}

  postulate A : Set
  postulate a : A

  record R (x : A) : Set where
    y : A
    y = a

  f : (@0 x : A) → R x → A
  f x r = R.y {x} r
  ```

Cubical Agda
------------

* [**Breaking**] The generation of Cubical Agda-specific support code was removed
  from `--without-K` and transferred to its own flag,
  `--cubical-compatible` (see
  [#5843](https://github.com/agda/agda/issues/5843) and
  [#6049](https://github.com/agda/agda/issues/6049) for the
  rationale).

  Note that code that uses (only) `--without-K` can no longer be
  imported from code that uses `--cubical`. Thus it may make sense to
  replace `--without-K` with `--cubical-compatible` in library code,
  if possible.

  Note also that Agda tends to be quite a bit faster if `--without-K`
  is used instead of `--cubical-compatible`.

  Note finally that when `--without-K` is used it might not be safe to
  compile and run programs that postulate erased univalence (but we
  are currently not aware of a program that would go wrong).

* Cubical Agda now has experimental support for indexed inductive types
  ([#3733](https://github.com/agda/agda/issues/3733)).
  See the [user guide](https://agda.readthedocs.io/en/latest/language/cubical.html#indexed-inductive-types)
  for caveats.

* The cubical interval `I` now belongs to its own sort, `IUniv`, rather
  than `SSet`. For `J : IUniv` and `A : J → Set l`, we have
  `(j : J) → A j : Set l`, that is, the type of functions from a type in `IUniv`
  to a fibrant type is fibrant.

* The option `--experimental-irrelevance` is now perhaps incompatible
  with Cubical Agda and perhaps also postulated univalence (see
  [#5611](https://github.com/agda/agda/issues/5611) and
  [#5861](https://github.com/agda/agda/pull/5861)).

  This is not meant to imply that the option was not already
  incompatible with those things. Note that
  `--experimental-irrelevance` cannot be used together with `--safe`.

* A new built-in constructor `REFLID` was added to the cubical identity
  types. This is definitionally equal to the reflexivity identification
  built with `conid`, with the difference being that matching on
  `REFLID` is allowed.

  ```agda
  symId : ∀ {a} {A : Set a} {x y : A} → Id x y → Id y x
  symId reflId = reflId
  ```

* Definitions which pattern match on higher-inductive types are no
  longer considered for injectivity analysis.
  ([#6219](https://github.com/agda/agda/pull/6219))

* [**Breaking**] Higher constructors are no longer considered as guarding in the productivity check.
  ([#6108](https://github.com/agda/agda/issues/6108))

* Rewrite rules with interval arguments are now supported.
  ([#4384](https://github.com/agda/agda/issues/4384))

The flat modality
-----------------

* [**Breaking**] The `@flat`/`@♭` modality is now by default disabled (see
  [#4927](https://github.com/agda/agda/issues/4927)).

  It can be enabled using the infective flag `--cohesion`.

* [**Breaking**] Matching on `@flat` arguments is now disabled by default, the flag
  `--no-flat-split` has been removed, and the flag `--flat-split` is
  now infective (see [#6238](https://github.com/agda/agda/issues/6238)
  and [#6263](https://github.com/agda/agda/issues/6263)).

  Matching can be enabled using the `--flat-split` flag. Note that in
  Cubical Agda functions that match on an argument marked with `@flat`
  trigger the `UnsupportedIndexedMatch` warning, and the code might
  not compute properly.

Reflection
----------

* Two new reflection primitives

  ```agda
  declareData      : Name → Nat → Type → TC ⊤
  defineData       : Name → List (Σ Name (λ _ → Type)) → TC ⊤
  ```

  are added for declaring and defining datatypes, similar to
  `declareDef` and `defineDef`.

* The construct `unquoteDecl` is extended with the ability of bringing
  a datatype `d` and its constructors `c₁ ... cₙ` given by a `TC`
  computation `m` into scope by the following syntax:

  ```agda
  unquoteDecl data x constructor c₁ .. cₙ = m
  ```

* A new reflection primitive `getInstances : Meta → TC (List Term)`
  was added to `Agda.Builtin.Reflection`. This operation returns the
  list of all possibly valid instance candidates for a given
  metavariable. For example, the following macro instantiates the goal
  with the first instance candidate, even if there are several:
  ```agda
  macro
    pickWhatever : Term → TC ⊤
    pickWhatever hole@(meta m _) = do
      (cand ∷ _) ← getInstances m
        where [] -> typeError (strErr "No candidates!" ∷ [])
      unify hole cand
    pickWhatever _ = typeError (strErr "Already solved!" ∷ [])
  ```

* [**Breaking**] The reflection primitives `getContext` and `inContext` use a nominal context
  `List (Σ String λ _ → Arg Type)` instead of  `List (Arg Type)` for printing
  type information better. Similarly, `extendContext` takes an extra argument
  of type `String`.

* `macro` definitions can now be used even when they are declared as erased.
  For example, this is now accepted:
  ```agda
  macro
    @0 trivial : Term → TC ⊤
    trivial = unify (con (quote refl) [])

  test : 42 ≡ 42
  test = trivial
  ```

* A new reflection primitive `formatErrorParts : List ErrorPart → TC String`
  is added. It takes a list of `ErrorPart` and return its formatted string.

* [**Breaking**] A new constructor `pattErr : Pattern → ErrorPart` of `ErrorPart` for reflection
  is added.

* [**Breaking**] The reflection primitives `getType` and
  `getDefinition` respect the module context they are invoked from
  instead of returning information that would be expected in the top
  context.

* [**Breaking**] The reflection primitive `inContext` cannot step
  outside of the context that the `TC` computation is invoked from
  anymore. The telescope is now relative to that context instead.

Syntax
------

* It is now OK to put lambda-bound variables anywhere in the
  right-hand side of a syntax declaration. However, there must always
  be at least one "identifier" between any two regular "holes". For
  instance, the following syntax declaration is accepted because `-`
  is between the holes `B` and `D`.

  ```agda
  postulate
    F : (Set → Set) → (Set → Set) → Set

  syntax F (λ A → B) (λ C → D) = B A C - D
  ```

* Syntax can now use lambdas with multiple arguments
  ([#394](https://github.com/agda/agda/issues/394)).

  Example:

  ```agda
  postulate
    Σ₂ : (A : Set) → (A → A → Set) → Set

  syntax Σ₂ A (λ x₁ x₂ → P) = [ x₁ x₂ ⦂ A ] × P
  ```

Builtins
--------

* [**Breaking**] Change `primFloatToWord64` to return `Maybe Word64`.
  (See [#6093](https://github.com/agda/agda/issues/6093).)

  The new type is
  ```agda
    primFloatToWord64 : Float → Maybe Word64
  ```
  and it returns `nothing` for `NaN`.

* [**Breaking**] The type expected by the builtin `EQUIVPROOF` has been changed to
  properly encode the condition that `EQUVIFUN` is an equivalence.
  ([#5661](https://github.com/agda/agda/issues/5661),
  [#6032](https://github.com/agda/agda/pull/6032))

* [**Breaking**] The primitive `primIdJ` has been removed
  ([#6032](https://github.com/agda/agda/pull/6032)) in favour of
  matching on the cubical identity type.

* [**Breaking**] The builtin `SUBIN` is now exported from `Agda.Builtin.Cubical.Sub` as
  **`inS`** rather than `inc`. Similarly, the internal modules refer to
  `primSubOut` as `outS`. ([#6032](https://github.com/agda/agda/pull/6032))

Pragmas and options
-------------------

* It is now possible to declare several `BUILTIN REWRITE` relations.
  Example:
  ```agda
  {-# OPTIONS --rewriting #-}

  open import Agda.Builtin.Equality
  open import Agda.Builtin.Equality.Rewrite  -- 1st rewrite relation

  postulate
    R : (A : Set) → A → A → Set
    A : Set
    a b c : A
    foo : R A a b  -- using 2nd rewrite relation
    bar : b ≡ c    -- using 1st rewrite relation

  {-# BUILTIN REWRITE R #-}  -- 2nd rewrite relation
  {-# REWRITE foo bar #-}

  test : a ≡ c
  test = refl
  ```

* [**Breaking**] Option `--experimental-lossy-unification` that turns on
  (the incomplete) first-order unification has been renamed to
  `--lossy-unification`.
  ([#1625](https://github.com/agda/agda/issues/1625))

* The new option `--no-load-primitives` complements `--no-import-sorts`
  by foregoing loading of the primitive modules altogether. This option
  leaves Agda in a very fragile state, as the built-in sorts are used
  extensively throughout the implementation. It is intended to be used
  by Literate Agda projects which want to bind `BUILTIN TYPE` (and
  other primitives) in their own literate files.

* If `--interaction-exit-on-error` is used, then Agda exits with a
  non-zero exit code if `--interaction` or `--interaction-json` are
  used and a type error is encountered. The option also makes Agda
  exit with exit code 113 if Agda fails to parse a command.

  This option might for instance be used if Agda is controlled from a
  script.

* Add a `NOT_PROJECTION_LIKE` pragma, which marks a function as not
  suitable for projection-likeness. Projection-like functions have some of
  their arguments erased, which can cause confusing behaviour when they
  are printed instantiated (see [#6203](https://github.com/agda/agda/issues/6203)).

* [**Breaking**] The options `--subtyping` and `--no-subtyping` have been removed
  (see [#5427](https://github.com/agda/agda/issues/5427)).

Profiling and performance
-------------------------

* New verbosity `-v debug.time:100` adds time stamps to debugging output.

* [**Breaking**] Profiling options are now turned on with a new `--profile` flag
  instead of abusing the debug verbosity option. (See
  [#5781](https://github.com/agda/agda/issues/5781).)

* The new profiling option `--profile=conversion` collects statistics
  on how often various steps of the conversion algorithm are used
  (reduction, eta-expansion, syntactic equality, etc).

* Meta-variables can now be saved in `.agdai` files, instead
  of being expanded. This can affect performance. (See
  [#5731](https://github.com/agda/agda/issues/5731).)

  Meta-variables are saved if the pragma option `--save-metas` is
  used. This option can be overridden by `--no-save-metas`.

* The new option `--syntactic-equality[=FUEL]` can be used to limit
  how many times the syntactic equality shortcut is allowed to fail
  (see [#5801](https://github.com/agda/agda/issues/5801)).

  If `FUEL` is omitted, then the syntactic equality shortcut is
  enabled without any restrictions.

  If `FUEL` is given, then the syntactic equality shortcut is given
  `FUEL` units of fuel. The exact meaning of this is
  implementation-dependent, but successful uses of the shortcut do not
  affect the amount of fuel. Currently the fuel is decreased in the
  failure continuations of the implementation of the syntactic
  equality shortcut. When a failure continuation completes the fuel is
  restored to its previous amount.

  The idea for this option comes from András Kovács'
  [smalltt](https://github.com/AndrasKovacs/smalltt/blob/989b020309686e04374f1ab7844f468386d2eb2f/README.md#approximate-conversion-checking).

  Note that this option is experimental and subject to change.

Library management
------------------

* Library files below the "project root" are now ignored
  (see [#5644](https://github.com/agda/agda/issues/5644)).

  For instance, if you have a module called `A.B.C` in the directory
  `Root/A/B`, then `.agda-lib` files in `Root/A` or `Root/A/B` do not
  affect what options are used to type-check `A.B.C`: `.agda-lib`
  files for `A.B.C` have to reside in `Root`, or further up the
  directory hierarchy.

Interaction
-----------

* Agsy ([automatic proof search](https://agda.readthedocs.io/en/latest/tools/auto.html)) can
  now be invoked in the right-hand-sides of copattern matching clauses.
  ([#5827](https://github.com/agda/agda/pull/5827))

Compiler backends
-----------------

* [**Breaking**] Both the GHC and JS backends now refuse to compile code that uses
  `--cubical`.

  Note that support for compiling code that uses `--erased-cubical`
  has been added to the GHC backend (see above).

* If the GHC backend is invoked when `--interaction` or
  `--interaction-json` is active (for instance when the Emacs mode is
  used), then GHC is now invoked from the directory containing the
  `MAlonzo` directory (see
  [#6194](https://github.com/agda/agda/issues/6194)).

  Before GHC was invoked from the Agda process's current working
  directory, and that is still the case if `--interaction` and
  `--interaction-json` are not used.

DOT backend
-----------

* The new option `--dependency-graph-include=LIBRARY` can be used to
  restrict the dependency graph to modules from one or more libraries
  (see [#5634](https://github.com/agda/agda/issues/5634)).

  Note that the module given on the command line might not be
  included.

* The generated graphs no longer contain "redundant" edges: if a
  module is imported both directly and indirectly, then the edge
  corresponding to the direct import is omitted.

JSON API
--------

* [**Breaking**] The JSON API now represents meta-variables differently, using
  objects containing two keys, `id` and `module`, both with values
  that are (natural) numbers. See
  [#5731](https://github.com/agda/agda/issues/5731).


Other issues closed
--------------------

For 2.6.3, the following issues were also closed (see [bug
tracker](https://github.com/agda/agda/issues)):

  - [#3986](https://github.com/agda/agda/issues/3986): Subtyping .A -> B <= A -> B leads to wrong ArgInfo
  - [#4103](https://github.com/agda/agda/issues/4103): Rewrite rule rejected because of projection likeness
  - [#4506](https://github.com/agda/agda/issues/4506): Lack of unicode support in locale may result in uncaught IOException
  - [#4725](https://github.com/agda/agda/issues/4725): Cubical Agda: Program rejected by termination checker due to moved dot pattern
  - [#4755](https://github.com/agda/agda/issues/4755): Rewrite rule on constructor uses wrong type for matching
  - [#4763](https://github.com/agda/agda/issues/4763): Cubical Agda: Unquote anonymous copattern involving path
  - [#5191](https://github.com/agda/agda/issues/5191): Unifier can use erased variables in non-erased data parameters
  - [#5257](https://github.com/agda/agda/issues/5257): Internal error when matching on user syntax with binding
  - [#5378](https://github.com/agda/agda/issues/5378): Internal error with tactic on record field
  - [#5448](https://github.com/agda/agda/issues/5448): Should the predicate be erasable in the subst rule (without-K)
  - [#5462](https://github.com/agda/agda/issues/5462): Internal error caused by a REWRITE on a projection-like function
  - [#5468](https://github.com/agda/agda/issues/5468): Disallow certain forms of pattern matching when an index is erased
  - [#5525](https://github.com/agda/agda/issues/5525): Duplicate entries in `executables` file lead to undefined behavior
  - [#5548](https://github.com/agda/agda/issues/5548): Agda infers an incorrect type with subtyping on
  - [#5551](https://github.com/agda/agda/issues/5551): Panic when showing module contents with pattern synonym
  - [#5563](https://github.com/agda/agda/issues/5563): Allow erased names in the type signatures of let-bound definitions
  - [#5577](https://github.com/agda/agda/issues/5577): The "Could not generate equivalence" warning is not always emitted
  - [#5581](https://github.com/agda/agda/issues/5581): Lexical error with tab character in literate Agda text
  - [#5589](https://github.com/agda/agda/issues/5589): Internal error with REWRITE of function from path
  - [#5681](https://github.com/agda/agda/issues/5681): Panic on record declaration with unknown sort
  - [#5702](https://github.com/agda/agda/issues/5702): Can't case split an `HitInt` with some already existing cases
  - [#5715](https://github.com/agda/agda/issues/5715): Reflection: Use `Telescope` for `getContext`, `inContext`, and `extendContext`
  - [#5727](https://github.com/agda/agda/issues/5727): Reducing universe levels before checking is not sufficient
  - [#5728](https://github.com/agda/agda/issues/5728): Internal error when pattern matching on `...` in with statement without providing a pattern match
  - [#5734](https://github.com/agda/agda/issues/5734): Relevance check in reflection
  - [#5751](https://github.com/agda/agda/issues/5751): json interaction produces Haskell output for SolveAll
  - [#5754](https://github.com/agda/agda/issues/5754): Internal error when compiling program with quoted metavariable
  - [#5760](https://github.com/agda/agda/issues/5760): Some code related to Cubical Agda runs also when the K rule is on
  - [#5763](https://github.com/agda/agda/issues/5763): Internal parser error using syntax rules
  - [#5765](https://github.com/agda/agda/issues/5765): Erasure check failure when pattern matching on refl in erased definition
  - [#5775](https://github.com/agda/agda/issues/5775): JSON interaction produces fully qualified terms
  - [#5794](https://github.com/agda/agda/issues/5794): Agsy/Auto crashes with `Prelude.!!: index too large`
  - [#5823](https://github.com/agda/agda/issues/5823): Singleton check loops on recursive eta record
  - [#5828](https://github.com/agda/agda/issues/5828): Agsy/Auto panics with `-r` in the presence of a pattern synonym
  - [#5845](https://github.com/agda/agda/issues/5845): Internal error caused by abstracting `variables`
  - [#5848](https://github.com/agda/agda/issues/5848): Internal error with `--confluence-check`
  - [#5850](https://github.com/agda/agda/issues/5850): Warn about useless hiding in `variable` declaration
  - [#5856](https://github.com/agda/agda/issues/5856): Lambda with irrefutable pattern is not rejected when used on Path
  - [#5868](https://github.com/agda/agda/issues/5868): Document --two-level
  - [#5875](https://github.com/agda/agda/issues/5875): Instance Search breaks Termination Highlighting
  - [#5891](https://github.com/agda/agda/issues/5891): SizeUniv : SizeUniv is inconsistent
  - [#5901](https://github.com/agda/agda/issues/5901): Use emacs --batch mode in agda-mode setup
  - [#5920](https://github.com/agda/agda/issues/5920): Erased constructors skipped in modality check
  - [#5922](https://github.com/agda/agda/issues/5922): Failure of termination checking for reflection-generated code due to data projections
  - [#5923](https://github.com/agda/agda/issues/5923): Internal error in rewriting
  - [#5944](https://github.com/agda/agda/issues/5944): Internal error in rewriting with --two-level
  - [#5953](https://github.com/agda/agda/issues/5953): Recursor of inductive-inductive type does not pass termination check in Cubical Agda
  - [#5955](https://github.com/agda/agda/issues/5955): Composition of Glue Type Causes Infinite Loop
  - [#5956](https://github.com/agda/agda/issues/5956): Cubical Agda crashes when printing empty system
  - [#5966](https://github.com/agda/agda/issues/5966): Improved performance by switching to `vector-hashtables`
  - [#5989](https://github.com/agda/agda/issues/5989): Dead-code elimination crashes function with private tactic argument
  - [#6003](https://github.com/agda/agda/issues/6003): de Bruijn index out of scope when rewriting
  - [#6006](https://github.com/agda/agda/issues/6006): Internal error rewriting with holes
  - [#6015](https://github.com/agda/agda/issues/6015): Pi types and Partial types should not be considered inter-convertible
  - [#6022](https://github.com/agda/agda/issues/6022): Private bindings in imported modules defeat check for binding of primIdFace/primIdPath
  - [#6042](https://github.com/agda/agda/issues/6042): De Bruijn index out of scope when rewriting without-K
  - [#6043](https://github.com/agda/agda/issues/6043): de Bruijn error on unexpected implicit argument
  - [#6059](https://github.com/agda/agda/issues/6059): Non-terminating function over tuples passed with `--termination-depth=2`
  - [#6066](https://github.com/agda/agda/issues/6066): Document the meaning of `pattern` without `no-eta-equality`
  - [#6067](https://github.com/agda/agda/issues/6067): Another de Bruijn error in rewriting
  - [#6073](https://github.com/agda/agda/issues/6073): Constraint solving does not honour singleton types
  - [#6074](https://github.com/agda/agda/issues/6074): piSort/funSort of IUniv should be blocked on the codomain
  - [#6076](https://github.com/agda/agda/issues/6076): Agda input mode (emacs): Minibuffer display for `\;` is strange
  - [#6080](https://github.com/agda/agda/issues/6080): A space leak due to absName
  - [#6082](https://github.com/agda/agda/issues/6082): Elaborate-and-give does not respect --postfix-projections
  - [#6095](https://github.com/agda/agda/issues/6095): Ambiguous pattern synonyms broken with anonymous module
  - [#6112](https://github.com/agda/agda/issues/6112): Internal error: non-confluent rewriting to singletons
  - [#6200](https://github.com/agda/agda/issues/6200): The reflection machinery does not treat the module telescope consistently
  - [#6203](https://github.com/agda/agda/issues/6203): Projection-likeness and instance arguments
  - [#6205](https://github.com/agda/agda/issues/6205): Internal error with `withReconstructed`
  - [#6244](https://github.com/agda/agda/issues/6244): Make `--no-load-primitives` not `--safe`
  - [#6250](https://github.com/agda/agda/issues/6250): Documentation says `--sized-types` is the default when it isn't
  - [#6257](https://github.com/agda/agda/issues/6257): Document options `--prop`, `--guarded`, and `--two-level`.
  - [#6265](https://github.com/agda/agda/issues/6265): Some options should be listed in `restartOptions`
  - [#6273](https://github.com/agda/agda/issues/6273): Missing highlighting when interleaved mutual is used
  - [#6276](https://github.com/agda/agda/issues/6276): LaTeX/HTML generation doesn't properly render parameters of pre-declared records
  - [#6281](https://github.com/agda/agda/issues/6281): Special treatment of attribute followed by underscore in pretty-printer
  - [#6285](https://github.com/agda/agda/issues/6285): Bump to GHC 9.4.3
  - [#6337](https://github.com/agda/agda/issues/6337): --lossy-unification in Agda 2.6.3
  - [#6338](https://github.com/agda/agda/issues/6338): internal error in Agda, perhaps related to --rewriting

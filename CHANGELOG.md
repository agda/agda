Release notes for Agda version 2.6.3
====================================

Highlights
----------

* Added support for [Erased Cubical
  Agda](https://agda.readthedocs.io/en/v2.6.3/language/cubical.html#cubical-agda-with-erased-glue),
  a variant of Cubical Agda that is supported by the GHC and
  JavaScript backends, under the flag `--erased-cubical`.

* Added a new flag `--cubical-compatible` to turn on generation of
  Cubical Agda-specific support code (previously this behaviour was
  part of `--without-K`).

  Since `--cubical-compatible` mode implies that functions should work
  with the preliminary support for [indexed inductive types in Cubical
  Agda](https://agda.readthedocs.io/en/v2.6.3/language/cubical.html#indexed-inductive-types),
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
  [here](https://github.com/agda/agda/issues/6049#issuecomment-1293698980).

Installation and infrastructure
-------------------------------

Agda supports GHC versions 8.0.2 to 9.4.2.

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

  The GHC and JS backends can compile code that uses
  `--erased-cubical` if the top-level module uses this flag.

  This feature is experimental.

* The parameter arguments of constructors and record fields are now
  marked as erased
  ([#4786](https://github.com/agda/agda/issues/4786)).

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

* The generation of Cubical Agda-specific support code was removed
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

* Higher constructors are no longer considered as guarding in the productivity check.
  ([#6108](https://github.com/agda/agda/issues/6108))

* Rewrite rules with interval arguments are now supported.
  ([#4384](https://github.com/agda/agda/issues/4384))

* Matching on `@flat` arguments is now disabled by default when the
  `--cubical-compatible` or `--without-K` flags are used. It can be
  enabled again using the `--flat-split` flag. Note that, when using
  Cubical Agda, functions which match on a `@flat` argument will not
  compute when applied to `transport`s (this will generate an
  `UnsupportedIndexedMatch` warning).

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

* The reflection primitives `getContext` and `inContext` use a nominal context
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

* A new constructor `pattErr : Pattern → ErrorPart` of `ErrorPart` for reflection
  is added.

Syntax declarations
-------------------

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

* Change `primFloatToWord64` to return `Maybe Word64`.
  (See [#6093](https://github.com/agda/agda/issues/6093).)

  The new type is
  ```agda
    primFloatToWord64 : Float → Maybe Word64
  ```
  and it returns `nothing` for `NaN`.

* The type expected by the builtin `EQUIVPROOF` has been changed to
  properly encode the condition that `EQUVIFUN` is an equivalence.
  ([#5661](https://github.com/agda/agda/issues/5661),
  [#6032](https://github.com/agda/agda/pull/6032))

* The primitive `primIdJ` has been removed
  ([#6032](https://github.com/agda/agda/pull/6032)) in favour of
  matching on the cubical identity type.

* The builtin `SUBIN` is now exported from `Agda.Builtin.Cubical.Sub` as
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

* Option `--experimental-lossy-unification` that turns on
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

* The options `--subtyping` and `--no-subtyping` have been removed
  (see [#5427](https://github.com/agda/agda/issues/5427)).

Profiling and performance
-------------------------

* New verbosity `-v debug.time:100` adds time stamps to debugging output.

* Profiling options are now turned on with a new `--profile` flag
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

* Both the GHC and JS backends now refuse to compile code that uses
  `--cubical`.

  Note that support for compiling code that uses `--erased-cubical`
  has been added to both backends (see above).

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

* The JSON API now represents meta-variables differently, using
  objects containing two keys, `id` and `module`, both with values
  that are (natural) numbers. See
  [#5731](https://github.com/agda/agda/issues/5731).

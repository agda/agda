Release notes for Agda version 2.6.4
====================================

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


Erasure
-------

* [**Breaking**] The new flag `--erasure` turns on support for erasure
  ([#6349](https://github.com/agda/agda/issues/6349)).

  This flag is infective.

  Unless this flag is active the following things are prohibited:
  * Use of the annotations `@0` and `@erased`.
  * Use of names defined in Cubical Agda in Erased Cubical Agda.
  * Use of the flag `--erase-record-parameters`.

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

Syntax
------

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

Instance arguments
------------------

* [**Breaking**] The algorithm for resolution of instance arguments
  has been simplified. It will now only rely on the type of instances
  to determine which candidate it should use, and no longer on their
  values.

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

* Most boolean options now have their opposite, e.g., `--allow-unsolved-metas` is complemented by `--no-allow-unsolved-metas`.
  With the opposite one can override a previously given option.
  Options given on the command line are overwritten by options given in the `.agda-lib` file,
  which in turn get overwritten by options given in the individual `.agda` file.

* Option `--flat-split` again implies `--cohesion`.
  Reverts change introduced in Agda 2.6.3 where `--cohesion` was a prerequisite for `--flat-split`.

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

Emacs mode
----------

* Helper function (`C-c C-h`) does not abstract over module parameters anymore
  (see [#2271](https://github.com/agda/agda/issues/2271)).

* New Agda input mode prefix `box` for APL boxed operators, e.g. `\box=` for ⌸;
  see PR [#6510](https://github.com/agda/agda/pull/6510/files) for full list of bindings.

Cubical Agda
------------

* Cubical Agda will now report boundary information for interaction
  points which are not at the top-level of their respective clauses.
  This includes bodies of `Path`-typed values, the faces of a partial
  element, arguments to functions returning paths, etc.

  Since this information is available in a structured way _during
  interaction_, the "goal type, context, and inferred type" command will
  also display the value of the expression at each relevant face.

  See also [PR #6529](https://github.com/agda/agda/pull/6529) for a
  deeper explanation and a demo video.

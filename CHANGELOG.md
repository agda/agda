Release notes for Agda version 2.6.3
====================================

Installation and infrastructure
-------------------------------

Agda supports GHC versions 8.0.2 to 9.2.1.

Language
--------

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
  Set} → D A`, and the type of the record field `R.f` is {@0 A : Set}
  → R A → A`:
  ```agda
  data D (A : Set) : Set where
    c : D A

  record R (A : Set) : Set where
    field
      f : A
  ```

* The options `--subtyping` and `--no-subtyping` have been removed
  (see [#5427](https://github.com/agda/agda/issues/5427)).

* The cubical interval `I` now belongs to its own sort, `IUniv`, rather
  than `SSet`. For `J : ISet` and `A : J → Set l`, we have
  `(j : J) → A : Set l`, that is, the type of functions from a type in `ISet`
  to a fibrant type is fibrant.

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

* The reflection primitives `getContext` and `inContext` use nominal context
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

Library management
------------------

* Library files below the "project root" are now ignored
  (see [#5644](https://github.com/agda/agda/issues/5644)).

  For instance, if you have a module called `A.B.C` in the directory
  `Root/A/B`, then `.agda-lib` files in `Root/A` or `Root/A/B` do not
  affect what options are used to type-check `A.B.C`: `.agda-lib`
  files for `A.B.C` have to reside in `Root`, or further up the
  directory hierarchy.

Compiler backends
-----------------

* Both the GHC and JS backends now refuse to compile code that uses
  `--cubical`.

  Note that support for compiling code that uses `--erased-cubical`
  has been added to both backends (see above).

LaTeX backend
-------------

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

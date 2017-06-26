Version TODO
============

The library has been tested using Agda version TODO.

Important changes since 0.13:

* Added support for GHC 8.0.2.

* Added `Category.Functor.Morphism` and module `Category.Functor.Identity`.

* Native (pattern-matching) definitions for `Data.Vec.map` and `Data.Vec.zipWith`.
  Previously they were defined using the `applicative` operations of `Vec`.
  The rationale for this change is better printing of goals involving `map`
  or `zipWith`.  Also, it has been argued that `zipWith` is fundamental than `_⊛_`.

  In the wake of this change, the following definitions have been added:
  1. `Data.Vec.functor`, encapsulating `Data.Vec.map`.
  2. The following properties in `Data.Vec.Properties`, relating old and new definition:
     ```
     ⊛-is-zipWith
     map-is-⊛
     zipWith-is-⊛
     ```
  3. The following new lemmata in `Data.Vec.Properties`:
     ```
     lookup-map
     lookup-functor-morphism
     map-replicate
     zipWith-replicate
     zipWith-map
     ```

* `Data.Container` and `Data.Container.Indexed` now allow for different
  levels in the container and in the data it contains.

* Added functions `punchIn` and `punchOut` to `Data.Fin`

* Added additional proofs to `Data.Fin.Properties`:
  ```agda
  isDecEquivalence
  
  ≤-reflexive, ≤-refl, ≤-trans, ≤-antisymmetric
  ≤-total, ≤-isPreorder, ≤-isPartialOrder, ≤-isTotalOrder

  _<?_, <-trans, <-isStrictTotalOrder
  
  punchOut-injective, punchIn-injective, punchIn-punchOut, punchInᵢ≢i
  ```

* Added additional proofs to `Data.Nat.Properties`:
  ```agda
  suc-injective

  ≤-reflexive, ≤-refl, ≤-trans, ≤-antisymmetric, ≤-total
  ≤-isPreorder, ≤-isPartialOrder, ≤-isTotalOrder, ≤-isDecTotalOrder

  _<?_,  <-transʳ, <-transˡ, <-irrefl, <-asym

  ⊓-idem, ⊔-idem
  m⊓n≤n, m≤m⊔n, m⊔n≤m+n, m⊓n≤m+n
  ⊔-mono-≤, ⊔-mono-<, ⊓-mono-≤, ⊓-mono-<
  +-distribˡ-⊔, +-distribʳ-⊔, +-distrib-⊔,
  +-distribˡ-⊓, +-distribʳ-⊓, +-distrib-⊓
  ```

* Moved module `≤-Reasoning` from `Data.Nat` to `Data.Nat.Properties`

* Moved `decTotalOrder` in `Data.Nat` to `≤-decTotalOrder` in
  `Data.Nat.Properties`

* Added decidability lemma `gcd?` to `Data.Nat.GCD`

* Moved `¬∀⟶∃¬` from `Relation.Nullary.Negation` to `Data.Fin.Dec`

* Useful lemmas and properties that were previously in private scope,
  either explicitly or within records, have been made public in several
  Properties.agda files. These include:
  ```agda
  Data.List.Any.Properties
  Data.Nat.Properties
  Data.Vec.All.Properties
  ```

* Added `+-left-identity` and `*-left-zero` to `Data.Nat.Properties.Simple`

* Changed `Data.Vec.All.All₂` to a native version which allows better
  pattern matching. The new version (and the associated proofs in
  `Data.Vec.All.Properties`) are more generic with respect to types and
  levels.

* Added extra properties relating `_++_` and `concat` to `All` and `All₂`
  in `Data.Vec.All.Properties`

* Added syntax for existential quantifiers as `∃[ x ] B` and `∄[ x ] B`.

Version 0.13
============

The library has been tested using Agda version 2.5.2.

Important changes since 0.12:

* Added the `Selective` property in `Algebra.FunctionProperties` as
  well as proofs of the selectivity of `min` and `max` in
  `Data.Nat.Properties`.

* Added `Relation.Binary.Product.StrictLex.×-total₂`, an alternative
  (non-degenerative) proof for totality, and renamed `×-total` to
  `x-total₁` in that module.

* Added the `length-filter` property to `Data.List.Properties` (the
  `filter` equivalent to the pre-existing `length-gfilter`).

* Added `_≤?_` decision procedure for `Data.Fin`.

* Added `allPairs` function to `Data.Vec`.

* Added additional properties of `_∈_` to `Data.Vec.Properties`:
  `∈-map`, `∈-++ₗ`, `∈-++ᵣ`, `∈-allPairs`.

* Added some `zip`/`unzip`-related properties to
  `Data.Vec.Properties`.

* Added an `All` predicate and related properties for `Data.Vec` (see
  `Data.Vec.All` and `Data.Vec.All.Properties`).

* Added order-theoretic lattices and some related properties in
  `Relation.Binary.Lattice` and `Relation.Binary.Properties`.

* Added symmetric and equivalence closures of binary relations in
  `Relation.Binary.SymmetricClosure` and
  `Relation.Binary.EquivalenceClosure`.

* Added `Congruent₁` and `Congruent₂` to `Algebra.FunctionProperties`.
  These are aliases for `_Preserves _≈_ ⟶ _≈_` and
  `_Preserves₂ _≈_ ⟶ _≈_ ⟶ _≈_` from `Relation.Binary.Core`.

* Useful lemmas and properties that were previously in private scope,
  either explicitly or within records, have been made public in several
  `Properties.agda` files. These include:

  ```agda
  Data.Bool.Properties

  Data.Fin.Properties

  Data.Integer.Properties
  Data.Integer.Addition.Properties
  Data.Integer.Multiplication.Properties
  ```

Version 0.12
============

The library has been tested using Agda version 2.5.1.

Important changes since 0.11:

* Added support for GHC 8.0.1.

Version 0.11
============

The library has been tested using Agda version 2.4.2.4.

Important changes since 0.10:

* `Relation.Binary.PropositionalEquality.TrustMe.erase` was added.

* Added `Data.Nat.Base.{_≤″_,_≥″_,_<″_,_>″_,erase}`,
  `Data.Nat.Properties.{≤⇒≤″,≤″⇒≤}`, `Data.Fin.fromℕ≤″`, and
  `Data.Fin.Properties.fromℕ≤≡fromℕ≤″`.

* The functions in `Data.Nat.DivMod` have been optimised.

* Turned on η-equality for `Record.Record`, removed
  `Record.Signature′` and `Record.Record′`.

* Renamed `Data.AVL.agda._⊕_sub1` to `pred[_⊕_]`.

Version 0.10
============

The library has been tested using Agda version 2.4.2.3.

Important changes since 0.9:

* Renamed `Data.Unit.Core` to `Data.Unit.NonEta`.

* Removed `Data.String.Core`. The module `Data.String.Base` now
  contains these definitions.

* Removed `Relation.Nullary.Core`. The module `Relation.Nullary` now
  contains these definitions directly.

* Inspect on steroids has been simplified (see
  `Relation.Binary.PropositionalEquality` and
  `Relation.Binary.HeterogeneousEquality`).

  The old version has been deprecated (see the above modules) and it
  will be removed in the next release.

* Using `Data.X.Base` modules.

  The `Data.X.Base` modules are used for cheaply importing a data type
  and the most common definitions. The use of these modules reduce
  type-checking and compilation times.

  At the moment, the modules added are:

  ```agda
  Data.Bool.Base
  Data.Char.Base
  Data.Integer.Base
  Data.List.Base
  Data.Maybe.Base
  Data.Nat.Base
  Data.String.Base
  Data.Unit.Base
  ```

  These modules are also cheap to import and can be considered basic:

  ```agda
  Data.BoundedVec.Inefficient
  Data.Empty
  Data.Product
  Data.Sign
  Data.Sum
  Function
  Level
  Relation.Binary
  Relation.Binary.PropositionalEquality.TrustMe
  Relation.Nullary
  ```

* Added singleton sets to `Relation.Unary`.

  There used to be an isomorphic definition of singleton sets in
  `Monad.Predicate`, this has been removed and the module has been
  cleaned up accordingly.

  The singleton set is also used to define generic operations (Plotkin
  and Power's terminology) in `Data.Container.Indexed.FreeMonad`.

* Proved properties of `Data.List.gfilter`. The following definitions
  have been added to Data.List.Properties:

  ```agda
  gfilter-just      : ... → gfilter just xs ≡ xs
  gfilter-nothing   : ... → gfilter (λ _ → nothing) xs ≡ []
  gfilter-concatMap : ... → gfilter f ≗ concatMap (fromMaybe ∘ f)
  ```

* New in `Data.Nat.Properties`:

  ```agda
  <⇒≤pred : ∀ {m n} → m < n → m ≤ pred n
  ```

* New in `Data.Fin`:

  ```agda
  strengthen : ∀ {n} (i : Fin n) → Fin′ (suc i)
  ```

* New in `Data.Fin.Properties`:

  ```agda
  from-to        : ∀ {n} (i : Fin n) → fromℕ (toℕ i) ≡ strengthen i
  toℕ-strengthen : ∀ {n} (i : Fin n) → toℕ (strengthen i) ≡ toℕ i

  fromℕ-def    : ∀ n → fromℕ n ≡ fromℕ≤ ℕ≤-refl
  reverse-suc  : ∀{n}{i : Fin n} → toℕ (reverse (suc i)) ≡ toℕ (reverse i)
  inject≤-refl : ∀ {n} (i : Fin n) (n≤n : n ℕ≤ n) → inject≤ i n≤n ≡ i
  ```

* New in `Data.List.NonEmpty`:

  ```agda
  foldr₁ : ∀ {a} {A : Set a} → (A → A → A) → List⁺ A → A
  foldl₁ : ∀ {a} {A : Set a} → (A → A → A) → List⁺ A → A
  ```

* `Data.AVL.Height-invariants._∼_` was replaced by `_∼_⊔_`, following
  Conor McBride's principle of pushing information into indices rather
  than pulling information out.

  Some lemmas in `Data.AVL.Height-invariants` (`1+`, `max∼max` and
  `max-lemma`) were removed.

  The implementations of some functions in `Data.AVL` were simplified.
  This could mean that they, and other functions depending on them (in
  `Data.AVL`, `Data.AVL.IndexedMap` and `Data.AVL.Sets`), reduce in a
  different way than they used to.

* The fixity of all `_∎` and `finally` operators, as well as
  `Category.Monad.Partiality.All._⟨_⟩P`, was changed from `infix 2` to
  `infix 3`.

* The fixity of `Category.Monad.Partiality._≟-Kind_`, `Data.AVL._∈?_`,
  `Data.AVL.IndexedMap._∈?_`, `Data.AVL.Sets._∈?_`, `Data.Bool._≟_`,
  `Data.Char._≟_`, `Data.Float._≟_`, `Data.Nat._≤?_`,
  `Data.Nat.Divisibility._∣?_`, `Data.Sign._≟_`, `Data.String._≟_`,
  `Data.Unit._≟_`, `Data.Unit._≤?_` and
  `Data.Vec.Equality.DecidableEquality._≟_` was changed from the
  default to `infix 4`.

* The fixity of all `_≟<something>_` operators in `Reflection` is now
  `infix 4` (some of them already had this fixity).

* The fixity of `Algebra.Operations._×′_` was changed from the default
  to `infixr 7`.

* The fixity of `Data.Fin.#_` was changed from the default to
  `infix 10`.

* The fixity of `Data.Nat.Divisibility.1∣_` and `_∣0` was changed from
  the default to `infix 10`.

* The fixity of `Data.Nat.DivMod._divMod_`, `_div_` and `_mod_` was
  changed from the default to `infixl 7`.

* The fixity of `Data.Product.Σ-syntax` was changed from the default
  to `infix 2`.

* The fixity of `Relation.Unary._~` was changed from the default to
  `infix 10`.

Version 0.9
===========

The library has been tested using Agda version 2.4.2.1.

Important changes since 0.8.1:

* `Data.List.NonEmpty`

  Non-empty lists are no longer defined in terms of
  `Data.Product._×_`, instead, now they are defined as record with
  fields head and tail.

* Reflection API

  + Quoting levels was fixed. This fix could break some code (see Agda
    Issue [#1207](https://github.com/agda/agda/issues/1269)).

  + The `Reflection.type` function returns a normalised
    `Reflection.Type` and `quoteTerm` returns an η-contracted
    `Reflection.Term` now. These changes could break some code (see
    Agda Issue [#1269](https://github.com/agda/agda/issues/1269)).

  + The primitive function for showing names, `primShowQName`, is now
    exposed as `Reflection.showName`.

* Removed compatibility modules for `Props -> Properties` rename

  Use `Foo.Properties.Bar` instead of `Foo.Props.Bar`.

Version 0.8.1
=============

The library has been tested using Agda version 2.4.2.

Important changes since 0.8:

* Reflection API

  Agda 2.4.2 added support for literals, function definitions, pattern
  matching lambdas and absurd clause/patterns (see Agda release
  notes). The new supported entities were added to the
  `Reflection.agda` module.

* Modules renamed

  `Foo.Props.Bar` -> `Foo.Properties.Bar`

  The current compatibility modules `Foo.Props.Bar` will be removed in
  the next release.

Version 0.8
===========

Version 0.8 of the
[standard library](http://wiki.portal.chalmers.se/agda/pmwiki.php?n=Libraries.StandardLibrary)
has now been released.

The library has been tested using Agda version 2.4.0.

Version 0.7
===========

Version 0.7 of the
[standard library](http://wiki.portal.chalmers.se/agda/pmwiki.php?n=Libraries.StandardLibrary)
has now been released.

The library has been tested using Agda version 2.3.2.

Version 0.6
===========

Version 0.6 of the
[standard library](http://wiki.portal.chalmers.se/agda/pmwiki.php?n=Libraries.StandardLibrary)
has now been released.

The library has been tested using Agda version 2.3.0.

Version 0.5
===========

Version 0.5 of the
[standard library](http://wiki.portal.chalmers.se/agda/pmwiki.php?n=Libraries.StandardLibrary)
has now been released.

The library has been tested using Agda version 2.2.10.

Version 0.4
===========

Version 0.4 of the
[standard library](http://wiki.portal.chalmers.se/agda/pmwiki.php?n=Libraries.StandardLibrary)
has now been released.

The library has been tested using Agda version 2.2.8.

Version 0.3
===========

Version 0.3 of the
[standard library](http://wiki.portal.chalmers.se/agda/pmwiki.php?n=Libraries.StandardLibrary)
has now been released.

The library has been tested using Agda version 2.2.6.

Version 0.2
===========

Version 0.2 of the
["standard" library](http://wiki.portal.chalmers.se/agda/pmwiki.php?n=Libraries.StandardLibrary)
has now been released.

The library has been tested using Agda version 2.2.4.

Note that the library sources are now located in the sub-directory
`lib-<version>/src` of the installation tarball.

Version 0.1
===========

Version 0.1 of the
["standard" library](http://wiki.portal.chalmers.se/agda/pmwiki.php?n=Libraries.StandardLibrary)
has now been released.

The library has been tested using Agda version 2.2.2.

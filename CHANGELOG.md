Version TODO
============

The library has been tested using Agda version TODO.

Important changes since 0.13:

Non-backwards compatible changes
--------------------------------

* Added native (pattern-matching) definitions for `Data.Vec.map` and `Data.Vec.zipWith`.
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

* Moved module `≤-Reasoning` from `Data.Nat` to `Data.Nat.Properties`

* Moved `decTotalOrder` in `Data.Nat` to `≤-decTotalOrder` in
  `Data.Nat.Properties`

* Moved `¬∀⟶∃¬` from `Relation.Nullary.Negation` to `Data.Fin.Dec`

* Moved internal modules `Membership` and `Membership-≡` out of
  `Data.List.Any` into `Data.List.Any.Membership` and
  `Data.List.Any.Membership.Propositional` respectively.

* Moved existing contents of `Data.List.Any.Membership` to
  `Data.List.Any.Membership.Propositional.Properties`

* Changed the implementation of `downFrom` in `Data.List` to a
  more idiomatic, easier-to-reason-about version.

* Changed `Data.Vec.All.All₂` to a native version which allows better
  pattern matching. The new version (and the associated proofs in
  `Data.Vec.All.Properties`) are more generic with respect to types and
  levels.
  
Backwards compatible changes
----------------------------

* Added support for GHC 8.0.2.

* Added `Category.Functor.Morphism` and module `Category.Functor.Identity`.

* The file `Data.Nat.Properties.Simple` is now deprecated. All proofs
  have been moved to `Data.Nat.Properties` where they should be used directly.
  The `Simple` file still exists and re-exports the proofs from
  `Data.Nat.Properties` for backwards compatability reasons but will be
  removed in some future release.
  
* `Data.Container` and `Data.Container.Indexed` now allow for different
  levels in the container and in the data it contains.

* Added new module `Data.Empty.Irrelevant` containing an irrelevant version of
  `⊥-elim`.
  
* Added syntax for existential quantifiers in `Data.Product`:
  ```agda
  ∃-syntax (λ x → B) = ∃[ x ] B
  ∄-syntax (λ x → B) = ∄[ x ] B
  ``` 

* Added additional properties to `Algebra.FunctionProperties`:
  ```agda
  LeftCancellative  _•_ = ∀ x {y z} → (x • y) ≈ (x • z) → y ≈ z
  RightCancellative _•_ = ∀ {x} y z → (y • x) ≈ (z • x) → y ≈ z
  Cancellative      _•_ = LeftCancellative _•_ × RightCancellative _•_
  ```

* Added additional functions to `Data.List`
  ```agda
  applyUpTo f n     ≈ f[0]   ∷ f[1]   ∷ ... ∷ f[n-1] ∷ []
  upTo n            ≈ 0      ∷ 1      ∷ ... ∷ n-1    ∷ []
  applyDownFrom f n ≈ f[n-1] ∷ f[n-2] ∷ ... ∷ f[0]   ∷ []
  tabulate f        ≈ f[0]   ∷ f[1]   ∷ ... ∷ f[n-1] ∷ []
  allFin n          ≈ 0f     ∷ 1f     ∷ ... ∷ n-1f   ∷ []
  ```

* Added additional functions to `Data.Fin`:
  ```agda
  punchIn  i j ≈ if j≥i then j+1 else j
  punchOut i j ≈ if j>i then j-1 else j
  ```

* Added additional proofs to `Data.Fin.Properties`:
  ```agda
  isDecEquivalence     : ∀ {n} → IsDecEquivalence (_≡_ {A = Fin n})

  ≤-reflexive          : ∀ {n} → _≡_ ⇒ (_≤_ {n})
  ≤-refl               : ∀ {n} → Reflexive (_≤_ {n})
  ≤-trans              : ∀ {n} → Transitive (_≤_ {n})
  ≤-antisymmetric      : ∀ {n} → Antisymmetric _≡_ (_≤_ {n})
  ≤-total              : ∀ {n} → Total (_≤_ {n})
  ≤-isPreorder         : ∀ {n} → IsPreorder _≡_ (_≤_ {n})
  ≤-isPartialOrder     : ∀ {n} → IsPartialOrder _≡_ (_≤_ {n})
  ≤-isTotalOrder       : ∀ {n} → IsTotalOrder _≡_ (_≤_ {n})

  _<?_                 : ∀ {n} → Decidable (_<_ {n})
  <-trans              : ∀ {n} → Transitive (_<_ {n})
  <-isStrictTotalOrder : ∀ {n} → IsStrictTotalOrder _≡_ (_<_ {n})

  punchOut-injective   : punchOut i≢j ≡ punchOut i≢k → j ≡ k
  punchIn-injective    : punchIn i j ≡ punchIn i k → j ≡ k
  punchIn-punchOut     : punchIn i (punchOut i≢j) ≡ j
  punchInᵢ≢i            : punchIn i j ≢ i
  ```

* Added additional proofs to `Data.Nat.Properties`:
  ```agda
  suc-injective        : ∀ {m n} → suc m ≡ suc n → m ≡ n
  ≡-isDecEquivalence   : IsDecEquivalence (_≡_ {A = ℕ})
  ≡-decSetoid          : DecSetoid _ _

  ≤-reflexive          : _≡_ ⇒ _≤_
  ≤-refl               : Reflexive _≤_
  ≤-trans              : Antisymmetric _≡_ _≤_
  ≤-antisymmetric      : Transitive _≤_
  ≤-total              : Total _≤_
  ≤-isPreorder         : IsPreorder _≡_ _≤_
  ≤-isPartialOrder     : IsPartialOrder _≡_ _≤_
  ≤-isTotalOrder       : IsTotalOrder _≡_ _≤_
  ≤-isDecTotalOrder    : IsDecTotalOrder _≡_ _≤_

  _<?_                 : Decidable _<_
  <-irrefl             : Irreflexive _≡_ _<_
  <-asym               : Asymmetric _<_
  <-transʳ             : Trans _≤_ _<_ _<_
  <-transˡ             : Trans _<_ _≤_ _<_
  <-isStrictTotalOrder : IsStrictTotalOrder _≡_ _<_
  
  +-left-identity      : LeftIdentity 0 _+_
  +-identity           : Identity 0 _+_
  cancel-+-right       : RightCancellative _+_
  +-cancellative       : Cancellative _+_
  +-isSemigroup        : IsSemigroup _≡_ _+_
  
  *-left-zero          : LeftZero 0 _*_
  *-zero               : Zero 0 _*_
  *-left-identity      : LeftIdentity 1 _*_
  *-right-identity     : RightIdentity 1 _*_
  *-identity           : Identity 1 _*_
  distribˡ-*-+         : _*_ DistributesOverˡ _+_
  distrib-*-+          : _*_ DistributesOver _+_
  *-isSemigroup        : IsSemigroup _≡_ _*_
  
  ⊓-idem               : Idempotent _⊓_
  ⊔-idem               : Idempotent _⊔_
  m⊓n≤n                : ∀ m n → m ⊓ n ≤ n
  m≤m⊔n                : ∀ m n → m ≤ m ⊔ n
  m⊔n≤m+n              : ∀ m n → m ⊔ n ≤ m + n
  m⊓n≤m+n              : ∀ m n → m ⊓ n ≤ m + n
  ⊔-mono-≤             : _⊔_ Preserves₂ _≤_ ⟶ _≤_ ⟶ _≤_
  ⊔-mono-<             : _⊔_ Preserves₂ _<_ ⟶ _<_ ⟶ _<_
  ⊓-mono-≤             : _⊓_ Preserves₂ _≤_ ⟶ _≤_ ⟶ _≤_
  ⊓-mono-<             : _⊓_ Preserves₂ _<_ ⟶ _<_ ⟶ _<_
  +-distribˡ-⊔         : _+_ DistributesOverˡ _⊔_
  +-distribʳ-⊔         : _+_ DistributesOverʳ _⊔_
  +-distrib-⊔          : _+_ DistributesOver _⊔_
  +-distribˡ-⊓         : _+_ DistributesOverˡ _⊓_
  +-distribʳ-⊓         : _+_ DistributesOverʳ _⊓_
  +-distrib-⊓          : _+_ DistributesOver _⊓_
  ⊔-isSemigroup        : IsSemigroup _≡_ _⊔_
  ⊓-isSemigroup        : IsSemigroup _≡_ _⊓_
  ⊓-⊔-isLattice        : IsLattice _≡_ _⊓_ _⊔_
  ```

* Added decidability relation to `Data.Nat.GCD`
  ```agda
  gcd? : (m n d : ℕ) → Dec (GCD m n d)
  ```

* Added "not-divisible-by" relation to `Data.Nat.Divisibility`
  ```agda
  m ∤ n = ¬ (m ∣ n)
  ```

* Added additional proofs to `Data.Nat.Divisibility`
  ```agda
  ∣-reflexive      : _≡_ ⇒ _∣_
  ∣-refl           : Reflexive _∣_
  ∣-trans          : Transitive _∣_
  ∣-antisym        : Antisymmetric _≡_ _∣_
  ∣-isPreorder     : IsPreorder _≡_ _∣_
  ∣-isPartialOrder : IsPartialOrder _≡_ _∣_
  ```

* Added additional proofs to `Data.List.Properties`
  ```agda
  map-cong₂      : All (λ x → f x ≡ g x) xs → map f xs ≡ map g xs
  foldr-++       : foldr f x (ys ++ zs) ≡ foldr f (foldr f x zs) ys
  foldl-++       : foldl f x (ys ++ zs) ≡ foldl f (foldl f x ys) zs
  foldr-∷ʳ       : foldr f x (ys ∷ʳ y) ≡ foldr f (f y x) ys
  foldl-∷ʳ       : foldl f x (ys ∷ʳ y) ≡ f (foldl f x ys) y
  reverse-foldr  : foldr f x (reverse ys) ≡ foldl (flip f) x ys
  reverse-foldr  : foldl f x (reverse ys) ≡ foldr (flip f) x ys
  length-reverse : length (reverse xs) ≡ length xs
  ```

* Added additional proofs to `Data.List.Any.Properties`
  ```agda
  lose∘find : uncurry′ lose (proj₂ (find p)) ≡ p
  find∘lose : find (lose x∈xs pp) ≡ (x , x∈xs , pp)
 
  ∃∈-Any    : (∃ λ x → x ∈ xs × P x) → Any P xs
 
  ⊎→        : Any P xs ⊎ Any Q xs → Any (λ x → P x ⊎ Q x) xs
  ⊎←        : Any (λ x → P x ⊎ Q x) xs → Any P xs ⊎ Any Q xs
  ×→        : Any P xs × Any Q ys → Any (λ x → Any (λ y → P x × Q y) ys) xs
  ×←        : Any (λ x → Any (λ y → P x × Q y) ys) xs → Any P xs × Any Q ys
 
  map⁺      : Any (P ∘ f) xs → Any P (map f xs)
  map⁻      : Any P (map f xs) → Any (P ∘ f) xs
  map⁺∘map⁻ : map⁺ (map⁻ p) ≡ p
  map⁻∘map⁺ : map⁻ (map⁺ p) ≡ p
  ```
  
* Added additional proofs to `Data.Vec.All.Properties`
  ```agda
  All-++⁺      : All P xs → All P ys → All P (xs ++ ys)
  All-++ˡ⁻     : All P (xs ++ ys) → All P xs
  All-++ʳ⁻     : All P (xs ++ ys) → All P ys
  All-++⁻      : All P (xs ++ ys) → All P xs × All P ys
  
  All₂-++⁺     : All₂ _~_ ws xs → All₂ _~_ ys zs → All₂ _~_ (ws ++ ys) (xs ++ zs)
  All₂-++ˡ⁻    : All₂ _~_ (ws ++ ys) (xs ++ zs) → All₂ _~_ ws xs
  All₂-++ʳ⁻    : All₂ _~_ (ws ++ ys) (xs ++ zs) → All₂ _~_ ys zs
  All₂-++⁻     : All₂ _~_ (ws ++ ys) (xs ++ zs) → All₂ _~_ ws xs × All₂ _~_ ys zs
 
  All-concat⁺  : All (All P) xss → All P (concat xss)
  All-concat⁻  : All P (concat xss) → All (All P) xss
 
  All₂-concat⁺ : All₂ (All₂ _~_) xss yss → All₂ _~_ (concat xss) (concat yss)
  All₂-concat⁻ : All₂ _~_ (concat xss) (concat yss) → All₂ (All₂ _~_) xss yss
  ```

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

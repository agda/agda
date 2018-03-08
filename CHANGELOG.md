Version TODO
============

The library has been tested using Agda version TODO.

Important changes since 0.14:

Non-backwards compatible changes
--------------------------------

#### Upgrade and overhaul of organisation of relations over data

* Relations over data have been moved from the `Relation` subtree to the `Data`
  subtree. In general the files have been moved from `Relation.Binary.X` to
  `Data.X.Relation`. The full list of moves is as follows:
  ```
  `Relation.Binary.List.Pointwise`       ↦ `Data.List.Relation.Pointwise`
  `Relation.Binary.List.StrictLex`       ↦ `Data.List.Relation.Lex.Strict`
  `Relation.Binary.List.NonStrictLex`    ↦ `Data.List.Relation.Lex.NonStrict`
  `Relation.Binary.Sum`                  ↦ `Data.Sum.Relation.Pointwise`
                                         | `Data.Sum.Relation.LeftOrder`
  `Relation.Binary.Sigma.Pointwise`      ↦ `Data.Product.Relation.Pointwise.Dependent'
  `Relation.Binary.Product.Pointwise`    ↦ `Data.Product.Relation.Pointwise.NonDependent`
  `Relation.Binary.Product.StrictLex`    ↦ `Data.Product.Relation.Lex.Strict`
  `Relation.Binary.Product.NonStrictLex` ↦ `Data.Product.Relation.Lex.NonStrict`
  `Relation.Binary.Vec.Pointwise`        ↦ `Data.Vec.Relation.Pointwise.Inductive`
                                         | `Data.Vec.Relation.Pointwise.Extensional`
  ```

  This aims to increase usability of the library because:
    1. it keeps all the definitions about particular data types in the same directory
    2. it provides a location to reason about how operations on the data types affect the
       relations over them (e.g. how `Pointwise` is affected by `map`)
    3. there is anecdotal evidence that many people were not aware of the existence
       of the relations in the old location. The new location should be discovered naturally.

  The old files in `Relation.Binary.X` still exist for backwards compatability reasons and
  re-export the contents of files' new location in `Data.X.Relation` but may be removed in some
  future release.

* The contents of `Relation.Binary.Sum` has been split into two modules
  `Data.Sum.Relation.Pointwise` and `Data.Sum.Relation.LeftOrder`

* The contents of `Relation.Binary.Vec.Pointwise` has been split into two modules
  `Data.Vec.Relation.Pointwise.Inductive` and `Data.Vec.Relation.Pointwise.Extensional`.

  The inductive form of `Pointwise` has been generalised so that technically it can apply to two
  vectors with different lengths (although in practice the lengths must turn out to be equal). This
  allows a much wider range of proofs such as the fact that `[]` is a right identity for `_++_`
  which was previously not possible to prove using the old definition. In order to ensure
  compatability with the `--without-K` option, the universe level of `Inductive.Pointwise`
  has been increased from `ℓ` to `a ⊔ b ⊔ ℓ`.

* `Data.Vec.Equality` has been almost entirely reworked into four separate modules
  inside `Data.Vec.Relation.Equality` (namely `Setoid`, `DecSetoid`, `Propositional`
  and `DecPropositional`). All four of them now use `Data.Vec.Relation.Pointwise.Inductive`
  as a base.

  The proofs from the submodule `UsingVecEquality` in `Data.Vec.Properties` have been moved
  to these four new modules.

* The datatype `All₂` has been removed from `Data.Vec.All`, along with associated proofs
  as it duplicates existing functionality in `Data.Vec.Relation.Pointwise.Inductive`.
  Unfortunately it is not possible to maintain backwards compatability due to dependency
  cycles.

* Added new modules
  `Data.List.Relation.Equality.(Setoid/DecSetoid/Propositional/DecPropositional)`.

#### Upgrade of `Data.AVL`

* `Data.AVL.Key` and `Data.AVL.Height` have been split out of `Data.AVL`
  therefore ensuring they are independent on the type of `Value` the tree contains.

* `Indexed` has been put into its own core module `Data.AVL.Indexed`, following the
  example of `Category.Monad.Indexed` and `Data.Container.Indexed`.

* These changes allow `map` to have a polymorphic type and so it is now possible
  to change the type of values contained in a tree when mapping over it.

#### Upgrade of `Algebra.Morphism`

* Previously `Algebra.Morphism` only provides an example of a `Ring` homomorphism which
  packs the homomorphism and the proofs that it behaves the right way.

  Instead we have adopted and `Algebra.Structures`-like approach with proof-only
  records parametrised by the homomorphism and the structures it acts on. This make
  it possible to define the proof requirement for e.g. a ring in terms of the proof
  requirements for its additive abelian group and multiplicative monoid.

#### Upgrade of `filter` and `partition` in `Data.List`

* The functions `filter` and `partition` in `Data.List.Base` now use decidable
  predicates instead of boolean-valued functions. The boolean versions discarded
  type information, and hence were difficult to use and prove
  properties about. The proofs have been updated and renamed accordingly.

  The old boolean versions still exist as `boolFilter` and `boolPartition` for
  backwards compatibility reasons, but are deprecated and may be removed in some
  future release. The old versions can be implemented via the new versions
  by passing the decidability proof `λ v → f v ≟ true` with `_≟_` from `Data.Bool`.

#### Overhaul of categorical interpretations of List and Vec

* New modules `Data.List.Categorical` and `Data.Vec.Categorical` have been added
  for the categorical interpretations of `List` and `Vec`.

  The following have been moved to `Data.List.Categorical`:

  - The module `Monad` from `Data.List.Properties` (renamed to `MonadProperties`)
  - The module `Applicative` from `Data.List.Properties`
  - `monad`, `monadZero`, `monadPlus` and monadic operators from `Data.List`

  The following has been moved to `Data.Vec.Categorical`:

  - `applicative` and `functor` from `Data.Vec`
  - `lookup-morphism` and `lookup-functor-morphism` from `Data.Vec.Properties`

#### Other

* Renamed `Data.Container.FreeMonad.do` and `Data.Container.Indexed.FreeMonad.do`
  to `inn` as Agda 2.5.4 now supports proper 'do' notation.

* Changed the fixity of `⋃` and `⋂` in `Relation.Unary` to make space for `_⊢_`.

* Changed `_|_` from `Data.Nat.Divisibility` from data to a record. Consequently,
  the two parameters are no longer implicit arguments of the constructor (but
  such values can be destructed using a let-binding rather than a with-clause).

* Names in `Data.Nat.Divisibility` now use the `divides` symbol (typed \\|) consistently.
  Previously a mixture of \\| and | was used.

* Moved the proof `eq?` from `Data.Nat` to `Data.Nat.Properties`

* The proofs that were called `+-monoˡ-<` and `+-monoʳ-<` in `Data.Nat.Properties`
  have been renamed `+-mono-<-≤` and `+-mono-≤-<` respectively. The original
  names are now used for proofs of left and right monotonicity of `_+_`.

* Moved the proof `monoid` from `Data.List` to `++-monoid` in `Data.List.Properties`.

Deprecated features
-------------------

The following renaming has occurred as part of a drive to improve consistency across
the library. The old names still exist and therefore all existing code should still
work, however they have been deprecated and use of the new names is encouraged. Although not
anticipated any time soon, they may eventually be removed in some future release of the library.

* In `Data.Bool.Properties`:
  ```agda
  ∧-∨-distˡ      ↦ ∧-distribˡ-∨
  ∧-∨-distʳ      ↦ ∧-distribʳ-∨
  distrib-∧-∨    ↦ ∧-distrib-∨
  ∨-∧-distˡ      ↦ ∨-distribˡ-∧
  ∨-∧-distʳ      ↦ ∨-distribʳ-∧
  ∨-∧-distrib    ↦ ∨-distrib-∧
  ∨-∧-abs        ↦ ∨-abs-∧
  ∧-∨-abs        ↦ ∧-abs-∨

  not-∧-inverseˡ ↦ ∧-inverseˡ
  not-∧-inverseʳ ↦ ∧-inverseʳ
  not-∧-inverse  ↦ ∧-inverse
  not-∨-inverseˡ ↦ ∨-inverseˡ
  not-∨-inverseʳ ↦ ∨-inverseʳ
  not-∨-inverse  ↦ ∨-inverse

  isCommutativeSemiring-∨-∧ ↦ ∨-∧-isCommutativeSemiring
  commutativeSemiring-∨-∧   ↦ ∨-∧-commutativeSemiring
  isCommutativeSemiring-∧-∨ ↦ ∧-∨-isCommutativeSemiring
  commutativeSemiring-∧-∨   ↦ ∧-∨-commutativeSemiring
  isBooleanAlgebra          ↦ ∨-∧-isBooleanAlgebra
  booleanAlgebra            ↦ ∨-∧-booleanAlgebra
  commutativeRing-xor-∧     ↦ xor-∧-commutativeRing

  proof-irrelevance         ↦ T-irrelevance
  ```

* In `Data.Fin.Properties`:
  ```agda
  cmp              ↦ <-cmp
  strictTotalOrder ↦ <-strictTotalOrder
  ```

* In `Data.Integer.Properties`:
  ```agda
  inverseˡ              ↦ +-inverseˡ
  inverseʳ              ↦ +-inverseʳ
  distribʳ              ↦ *-distribʳ-+
  isCommutativeSemiring ↦ +-*-isCommutativeSemiring
  commutativeRing       ↦ +-*-commutativeRing
  *-+-right-mono        ↦ *-monoʳ-≤-pos
  cancel-*-+-right-≤    ↦ *-cancelʳ-≤-pos
  cancel-*-right        ↦ *-cancelʳ-≡
  doubleNeg             ↦ neg-involutive
  -‿involutive          ↦ neg-involutive
  +-⊖-left-cancel       ↦ +-cancelˡ-⊖
  ```

* In `Data.List.Base`:
  ```agda
  gfilter ↦  mapMaybe
  ```

* In `Data.List.Properties`:
  ```agda
  right-identity-unique ↦ ++-identityʳ-unique
  left-identity-unique  ↦ ++-identityˡ-unique
  ```

* In `Data.List.Relation.Pointwise`:
  ```agda
  Rel    ↦ Pointwise
  Rel≡⇒≡ ↦ Pointwise-≡⇒≡
  ≡⇒Rel≡ ↦ ≡⇒Pointwise-≡
  Rel↔≡  ↦ Pointwise-≡↔≡
  ```

* In `Data.Nat.Properties`:
  ```agda
  ¬i+1+j≤i ↦ i+1+j≰i
  ≤-steps  ↦ ≤-stepsˡ
  ```

* In all modules in the `Data.(Product/Sum).Relation` folders, all proofs with
  names using infix notation have been deprecated in favour of identical
  non-infix names, e.g.
  ```
  _×-isPreorder_ ↦ ×-isPreorder
  ```

* In `Data.Product.Relation.Lex.(Non)Strict`:
  ```agda
  ×-≈-respects₂ ↦ ×-respects₂
  ```

* In `Data.Product.Relation.Pointwise.Dependent`:
  ```agda
  Rel    ↦ Pointwise
  Rel↔≡  ↦ Pointwise-≡↔≡
  ```

* In `Data.Product.Relation.Pointwise.NonDependent`:
  ```agda
  _×-Rel_         ↦ Pointwise
  Rel↔≡           ↦ Pointwise-≡↔≡
  _×-≈-respects₂_ ↦ ×-respects₂
  ```

* In `Data.Sign.Properties`:
  ```agda
  opposite-not-equal ↦ s≢opposite[s]
  opposite-cong      ↦ opposite-injective
  cancel-*-left      ↦ *-cancelˡ-≡
  cancel-*-right     ↦ *-cancelʳ-≡
  *-cancellative     ↦ *-cancel-≡
  ```

* In `Data.Vec.Properties`:
  ```agda
  proof-irrelevance-[]= ↦ []=-irrelevance
  ```

* In `Data.Vec.Relation.Pointwise.Inductive`:
  ```agda
  Pointwise-≡ ↦ Pointwise-≡↔≡
  ```

* In `Data.Vec.Relation.Pointwise.Extensional`:
  ```agda
  Pointwise-≡ ↦ Pointwise-≡↔≡
  ```

* In `Induction.Nat`:
  ```agda
  rec-builder      ↦ recBuilder
  cRec-builder     ↦ cRecBuilder
  <′-rec-builder   ↦ <′-recBuilder
  <-rec-builder    ↦ <-recBuilder
  ≺-rec-builder    ↦ ≺-recBuilder
  <′-well-founded  ↦ <′-wellFounded
  <′-well-founded′ ↦ <′-wellFounded′
  <-well-founded   ↦ <-wellFounded
  ≺-well-founded   ↦ ≺-wellFounded
  ```

* In `Induction.WellFounded`:
  ```agda
  Well-founded                       ↦ WellFounded
  Some.wfRec-builder                 ↦ Some.wfRecBuilder
  All.wfRec-builder                  ↦ All.wfRecBuilder
  Subrelation.well-founded           ↦ Subrelation.wellFounded
  InverseImage.well-founded          ↦ InverseImage.wellFounded
  TransitiveClosure.downwards-closed ↦ TransitiveClosure.downwardsClosed
  TransitiveClosure.well-founded     ↦ TransitiveClosure.wellFounded
  Lexicographic.well-founded         ↦ Lexicographic.wellFounded
  ```

* In `Relation.Binary.PropositionalEquality`:
  ```agda
  proof-irrelevance     ↦ ≡-irrelevance
  ```

Removed features
----------------

#### Deprecated in version 0.10

* Modules `Deprecated-inspect` and `Deprecated-inspect-on-steroids` in `Relation.Binary.PropositionalEquality`.

* Module `Deprecated-inspect-on-steroids` in `Relation.Binary.HeterogeneousEquality`.

Backwards compatible changes
----------------------------

* Added support for GHC 8.2.2.

* Added new module `Data.Table`. A `Table` is a fixed-length collection of objects
  similar to a `Vec` from `Data.Vec`, but implemented as a function `Fin n → A`.
  This prioritises ease of lookup as opposed to `Vec` which prioritises the ease
  of adding and removing elements.

* The contents of the following modules are now more polymorphic with respect to levels:
  ```agda
  Data.Covec
  Data.List.Relation.Lex.Strict
  Data.List.Relation.Lex.NonStrict
  Data.Vec.Properties
  Data.Vec.Relation.Pointwise.Inductive
  Data.Vec.Relation.Pointwise.Extensional
  ```

* Added new proof to `asymmetric : Asymmetric _<_` to the `IsStrictPartialOrder` record.

* Added new proofs to `Data.AVL`:
  ```agda
  leaf-injective     : leaf p ≡ leaf q → p ≡ q
  node-injective-key : node k₁ lk₁ ku₁ bal₁ ≡ node k₂ lk₂ ku₂ bal₂ → k₁ ≡ k₂
  node-injectiveˡ    : node k lk₁ ku₁ bal₁ ≡ node k lk₂ ku₂ bal₂ → lk₁ ≡ lk₂
  node-injectiveʳ    : node k lk₁ ku₁ bal₁ ≡ node k lk₂ ku₂ bal₂ → ku₁ ≡ ku₂
  node-injective-bal : node k lk₁ ku₁ bal₁ ≡ node k lk₂ ku₂ bal₂ → bal₁ ≡ bal₂
  ```

* Added new proofs to `Data.Bin`:
  ```agda
  less-injective : (b₁ < b₂ ∋ less lt₁) ≡ less lt₂ → lt₁ ≡ lt₂
  ```

* Added new proofs to `Data.Bool.Properties`:
  ```agda
  ∨-identityˡ           : LeftIdentity false _∨_
  ∨-identityʳ           : RightIdentity false _∨_
  ∨-identity            : Identity false _∨_
  ∨-zeroˡ               : LeftZero true _∨_
  ∨-zeroʳ               : RightZero true _∨_
  ∨-zero                : Zero true _∨_
  ∨-idem                : Idempotent _∨_
  ∨-sel                 : Selective _∨_
  ∨-isSemigroup         : IsSemigroup _≡_ _∨_
  ∨-isCommutativeMonoid : IsCommutativeMonoid _≡_ _∨_ false

  ∧-identityˡ           : LeftIdentity true _∧_
  ∧-identityʳ           : RightIdentity true _∧_
  ∧-identity            : Identity true _∧_
  ∧-zeroˡ               : LeftZero false _∧_
  ∧-zeroʳ               : RightZero false _∧_
  ∧-zero                : Zero false _∧_
  ∧-idem                : Idempotent _∧_
  ∧-sel                 : Selective _∧_
  ∧-isSemigroup         : IsSemigroup _≡_ _∧_
  ∧-isCommutativeMonoid : IsCommutativeMonoid _≡_ _∧_ true

  ∨-∧-isLattice             : IsLattice _≡_ _∨_ _∧_
  ∨-∧-isDistributiveLattice : IsDistributiveLattice _≡_ _∨_ _∧_
  ```

* Added missing bindings to functions on `Data.Char.Base`:
  ```agda
  isLower    : Char → Bool
  isDigit    : Char → Bool
  isAlpha    : Char → Bool
  isSpace    : Char → Bool
  isAscii    : Char → Bool
  isLatin1   : Char → Bool
  isPrint    : Char → Bool
  isHexDigit : Char → Bool
  toNat      : Char → ℕ
  fromNat    : ℕ → Char
  ```

* Added new proofs to `Data.Cofin`:
  ```agda
  suc-injective : (Cofin (suc m) ∋ suc p) ≡ suc q → p ≡ q
  ```

* Added new proofs to `Data.Colist`:
  ```agda
  ∷-injectiveˡ    : (Colist A ∋ x ∷ xs) ≡ y ∷ ys → x ≡ y
  ∷-injectiveʳ    : (Colist A ∋ x ∷ xs) ≡ y ∷ ys → xs ≡ ys
  here-injective  : (Any P (x ∷ xs) ∋ here p) ≡ here q → p ≡ q
  there-injective : (Any P (x ∷ xs) ∋ there p) ≡ there q → p ≡ q
  ∷-injectiveˡ    : (All P (x ∷ xs) ∋ px ∷ pxs) ≡ qx ∷ qxs → px ≡ qx
  ∷-injectiveʳ    : (All P (x ∷ xs) ∋ px ∷ pxs) ≡ qx ∷ qxs → pxs ≡ qxs
  ∷-injective     : (Finite (x ∷ xs) ∋ x ∷ p) ≡ x ∷ q → p ≡ q
  ∷-injective     : (Infinite (x ∷ xs) ∋ x ∷ p) ≡ x ∷ q → p ≡ q
  ```

* Added new operations and proofs to `Data.Conat`:
  ```agda
  pred            : Coℕ → Coℕ

  suc-injective   : (Coℕ ∋ suc m) ≡ suc n → m ≡ n
  fromℕ-injective : fromℕ m ≡ fromℕ n → m ≡ n
  suc-injective   : (suc m ≈ suc n ∋ suc p) ≡ suc q → p ≡ q
  ```

* Added new proofs to `Data.Covec`:
  ```agda
  ∷-injectiveˡ : (Covec A (suc n) ∋ a ∷ as) ≡ b ∷ bs → a ≡ b
  ∷-injectiveʳ : (Covec A (suc n) ∋ a ∷ as) ≡ b ∷ bs → as ≡ bs
  ```

* Added new proofs to `Data.Fin.Properties`:
  ```agda
  ≤-isDecTotalOrder : ∀ {n} → IsDecTotalOrder _≡_ (_≤_ {n})
  ≤-irrelevance     : ∀ {n} → IrrelevantRel (_≤_ {n})

  <-asym            : ∀ {n} → Asymmetric (_<_ {n})
  <-irrefl          : ∀ {n} → Irreflexive _≡_ (_<_ {n})
  <-irrelevance     : ∀ {n} → IrrelevantRel (_<_ {n})
  ```

* Added new proofs to `Data.Integer.Properties`:
  ```agda
  +-cancelˡ-⊖       : (a + b) ⊖ (a + c) ≡ b ⊖ c
  neg-minus-pos     : -[1+ m ] - (+ n) ≡ -[1+ (m + n) ]
  [+m]-[+n]≡m⊖n     : (+ m) - (+ n) ≡ m ⊖ n
  ∣m-n∣≡∣n-m∣       : ∣ m - n ∣ ≡ ∣ n - m ∣
  +-minus-telescope : (m - n) + (n - o) ≡ m - o
  pos-distrib-*     : ∀ x y → (+ x) * (+ y) ≡ + (x * y)

  ≤-irrelevance     : IrrelevantRel _≤_
  <-irrelevance     : IrrelevantRel _<_
  ```

* Added new combinators to `Data.List.Base`:
  ```agda
  lookup    : (xs : List A) → Fin (length xs) → A
  unzipWith : (A → B × C) → List A → List B × List C
  unzip     : List (A × B) → List A × List B
  ```

* Added new proofs to `Data.List.Properties`:
  ```agda
  ∷-injectiveˡ      : x ∷ xs ≡ y List.∷ ys → x ≡ y
  ∷-injectiveʳ      : x ∷ xs ≡ y List.∷ ys → xs ≡ ys
  ∷ʳ-injectiveˡ     : xs ∷ʳ x ≡ ys ∷ʳ y → xs ≡ ys
  ∷ʳ-injectiveʳ     : xs ∷ʳ x ≡ ys ∷ʳ y → x ≡ y

  ++-assoc          : Associative {A = List A} _≡_ _++_
  ++-identityˡ      : LeftIdentity _≡_ [] _++_
  ++-identityʳ      : RightIdentity _≡_ [] _++_
  ++-identity       : Identity _≡_ [] _++_
  ++-isSemigroup    : IsSemigroup {A = List A} _≡_ _++_
  ++-isMonoid       : IsMonoid {A = List A} _≡_ _++_ []
  ++-semigroup      : ∀ {a} (A : Set a) → Semigroup _ _
  ++-monoid         : ∀ {a} (A : Set a) → Monoid _ _

  filter-all        : All P xs → dfilter P? xs ≡ xs
  filter-none       : All (¬_ ∘ P) xs → dfilter P? xs ≡ []

  tabulate-cong     : f ≗ g → tabulate f ≡ tabulate g
  tabulate-lookup   : tabulate (lookup xs) ≡ xs

  zipWith-identityˡ : ∀ xs → zipWith f [] xs ≡ []
  zipWith-identityʳ : ∀ xs → zipWith f xs [] ≡ []
  zipWith-comm      : (∀ x y → f x y ≡ f y x) → zipWith f xs ys ≡ zipWith f ys xs
  zipWith-unzipWith : uncurry′ g ∘ f ≗ id → uncurry′ (zipWith g) ∘ (unzipWith f)  ≗ id
  zipWith-map       : zipWith f (map g xs) (map h ys) ≡ zipWith (λ x y → f (g x) (h y)) xs ys
  map-zipWith       : map g (zipWith f xs ys) ≡ zipWith (λ x y → g (f x y)) xs ys
  length-zipWith    : length (zipWith f xs ys) ≡ length xs ⊓ length ys

  length-unzipWith₁ : length (proj₁ (unzipWith f xys)) ≡ length xys
  length-unzipWith₂ : length (proj₂ (unzipWith f xys)) ≡ length xys
  ```

* Added new proofs to `Data.List.All.Properties`:
  ```agda
  All-irrelevance : IrrelevantPred P → IrrelevantPred (All P)
  filter⁺₁        : All P (filter P? xs)
  filter⁺₂        : All Q xs → All Q (filter P? xs)
  mapMaybe⁺       : All (Maybe.All P) (map f xs) → All P (mapMaybe f xs)
  zipWith⁺        : Pointwise (λ x y → P (f x y)) xs ys → All P (zipWith f xs ys)
  ```

* Added new proofs to `Data.List.Any.Properties`:
  ```agda
  mapMaybe⁺ : Any (Maybe.Any P) (map f xs) → Any P (mapMaybe f xs)
  ```

* Added new proofs to `Data.List.Relation.Lex.NonStrict`:
  ```agda
  <-antisymmetric : Symmetric _≈_ → Antisymmetric _≈_ _≼_ → Antisymmetric _≋_ _<_
  <-transitive    : IsPartialOrder _≈_ _≼_ → Transitive _<_
  <-resp₂         : IsEquivalence _≈_ → _≼_ Respects₂ _≈_ → _<_ Respects₂ _≋_

  ≤-antisymmetric : Symmetric _≈_ → Antisymmetric _≈_ _≼_ → Antisymmetric _≋_ _≤_
  ≤-transitive    : IsPartialOrder _≈_ _≼_ → Transitive _≤_
  ≤-resp₂         : IsEquivalence _≈_ → _≼_ Respects₂ _≈_ → _≤_ Respects₂ _≋_
  ```

* Added new proofs to `Data.List.Relation.Pointwise`:
  ```agda
  tabulate⁺ : (∀ i → f i ∼ g i) → Pointwise _∼_ (tabulate f) (tabulate g)
  tabulate⁻ : Pointwise _∼_ (tabulate f) (tabulate g) → (∀ i → f i ∼ g i)
  ++⁺       : Pointwise _∼_ ws xs → Pointwise _∼_ ys zs → Pointwise _∼_ (ws ++ ys) (xs ++ zs)
  concat⁺   : Pointwise (Pointwise _∼_) xss yss → Pointwise _∼_ (concat xss) (concat yss)
  ```

* Added new proofs to `Data.List.Relation.Lex.Strict`:
  ```agda
  <-antisymmetric : Symmetric _≈_ → Irreflexive _≈_ _≺_ →  Asymmetric _≺_ → Antisymmetric _≋_ _<_
  <-transitive    : IsEquivalence _≈_ → _≺_ Respects₂ _≈_ → Transitive _≺_ → Transitive _<_
  <-respects₂     : IsEquivalence _≈_ → _≺_ Respects₂ _≈_ → _<_ Respects₂ _≋_

  ≤-antisymmetric : Symmetric _≈_ → Irreflexive _≈_ _≺_ →  Asymmetric _≺_ → Antisymmetric _≋_ _≤_
  ≤-transitive    : IsEquivalence _≈_ → _≺_ Respects₂ _≈_ → Transitive _≺_ → Transitive _≤_
  ≤-respects₂     : IsEquivalence _≈_ → _≺_ Respects₂ _≈_ → _≤_ Respects₂ _≋_
  ```

* Added new proofs to `Data.Maybe.Base`:
  ```agda
  just-injective : (Maybe A ∋ just a) ≡ just b → a ≡ b
  ```

* Added new proofs to `Data.Nat.Divisibility`:
  ```agda
  m|m*n   : m ∣ m * n
  ∣m⇒∣m*n : i ∣ m → i ∣ m * n
  ∣n⇒∣m*n : i ∣ n → i ∣ m * n
  ```

* Added new proofs to `Data.Nat.Properties`:
  ```agda
  ≤⇒≯                   : _≤_ ⇒ _≯_
  n≮n                   : ∀ n → n ≮ n
  ≤-stepsʳ              : ∀ m ≤ n → m ≤ n + o
  ≤-irrelevance         : IrrelevantRel _≤_
  <-irrelevance         : IrrelevantRel _<_

  +-monoˡ-≤             : ∀ n → (_+ n) Preserves _≤_ ⟶ _≤_
  +-monoʳ-≤             : ∀ n → (n +_) Preserves _≤_ ⟶ _≤_
  +-monoˡ-<             : ∀ n → (_+ n) Preserves _<_ ⟶ _<_
  +-monoʳ-<             : ∀ n → (n +_) Preserves _<_ ⟶ _<_
  +-semigroup           : Semigroup _ _
  +-0-monoid            : Monoid _ _
  +-0-commutativeMonoid : CommutativeMonoid _ _

  *-monoˡ-≤             : ∀ n → (_* n) Preserves _≤_ ⟶ _≤_
  *-monoʳ-≤             : ∀ n → (n *_) Preserves _≤_ ⟶ _≤_
  *-semigroup           : Semigroup _ _
  *-1-monoid            : Monoid _ _
  *-1-commutativeMonoid : CommutativeMonoid _ _
  *-+-semiring          : Semiring _ _

  ^-identityʳ           : RightIdentity 1 _^_
  ^-zeroˡ               : LeftZero 1 _^_
  ^-semigroup-morphism  : (x ^_) Is +-semigroup -Semigroup⟶ *-semigroup
  ^-monoid-morphism     : (x ^_) Is +-0-monoid -Monoid⟶ *-1-monoid

  m≤n⇒m⊓n≡m             : m ≤ n → m ⊓ n ≡ m
  m≤n⇒n⊓m≡m             : m ≤ n → n ⊓ m ≡ m
  m≤n⇒n⊔m≡n             : m ≤ n → n ⊔ m ≡ n
  m≤n⇒m⊔n≡n             : m ≤ n → m ⊔ n ≡ n
  ⊔-monoˡ-≤             : ∀ n → (_⊔ n) Preserves _≤_ ⟶ _≤_
  ⊔-monoʳ-≤             : ∀ n → (n ⊔_) Preserves _≤_ ⟶ _≤_
  ⊓-monoˡ-≤             : ∀ n → (_⊓ n) Preserves _≤_ ⟶ _≤_
  ⊓-monoʳ-≤             : ∀ n → (n ⊓_) Preserves _≤_ ⟶ _≤_
  m∸n+n≡m               : n ≤ m → (m ∸ n) + n ≡ m
  m∸[m∸n]≡n             : n ≤ m → m ∸ (m ∸ n) ≡ n

  s≤s-injective         : s≤s p ≡ s≤s q → p ≡ q
  ≤′-step-injective     : ≤′-step p ≡ ≤′-step q → p ≡ q
  ```

* Added new proofs to `Data.Plus`:
  ```agda
  []-injective    : (x [ _∼_ ]⁺ y ∋ [ p ]) ≡ [ q ] → p ≡ q
  ∼⁺⟨⟩-injectiveˡ : (x [ _∼_ ]⁺ z ∋ x ∼⁺⟨ p ⟩ q) ≡ (x ∼⁺⟨ r ⟩ s) → p ≡ r
  ∼⁺⟨⟩-injectiveʳ : (x [ _∼_ ]⁺ z ∋ x ∼⁺⟨ p ⟩ q) ≡ (x ∼⁺⟨ r ⟩ s) → q ≡ s
  ```

* Added new combinator to `Data.Product`:
  ```agda
  curry′ : (A × B → C) → (A → B → C)
  ```

* Added new proofs to `Data.Product.Properties`:
  ```agda
  ,-injectiveˡ : (a , b) ≡ (c , d) → a ≡ c
  ,-injectiveʳ : (Σ A B ∋ (a , b)) ≡ (a , c) → b ≡ c
  ```

* Added new operator in `Data.Product.Relation.Pointwise.NonDependent`:
  ```agda
  _×ₛ_ : Setoid ℓ₁ ℓ₂ → Setoid ℓ₃ ℓ₄ → Setoid _ _
  ```

* Added new proofs to `Data.Rational.Properties`:
  ```agda
  ≤-irrelevance : IrrelevantRel _≤_
  ```

* Added new proofs to `Data.ReflexiveClosure`:
  ```agda
  []-injective : (Refl _∼_ x y ∋ [ p ]) ≡ [ q ] → p ≡ q
  ```

* Added new proofs to `Data.Sign`:
  ```agda
  *-isSemigroup : IsSemigroup _≡_ _*_
  *-semigroup   : Semigroup _ _
  *-isMonoid    : IsMonoid _≡_ _*_ +
  *-monoid      : Monoid _ _
  ```

* Added new proofs to `Data.Star.Properties`:
  ```agda
  ◅-injectiveˡ : (Star T i k ∋ x ◅ xs) ≡ y ◅ ys → x ≡ y
  ◅-injectiveʳ : (Star T i k ∋ x ◅ xs) ≡ y ◅ ys → xs ≡ ys
  ```

* Added new proofs to `Data.Sum.Properties`:
  ```agda
  inj₁-injective : (A ⊎ B ∋ inj₁ x) ≡ inj₁ y → x ≡ y
  inj₂-injective : (A ⊎ B ∋ inj₂ x) ≡ inj₂ y → x ≡ y
  ```

* Added new operator in `Data.Sum.Relation.Pointwise`:
  ```agda
  _⊎ₛ_ : Setoid ℓ₁ ℓ₂ → Setoid ℓ₃ ℓ₄ → Setoid _ _
  ```

* Added new proofs to `Data.Vec.Properties`:
  ```agda
  ∷-injectiveˡ     : x ∷ xs ≡ y ∷ ys → x ≡ y
  ∷-injectiveʳ     : x ∷ xs ≡ y ∷ ys → xs ≡ ys

  []=⇒lookup       : xs [ i ]= x → lookup i xs ≡ x
  lookup⇒[]=       : lookup i xs ≡ x → xs [ i ]= x
  lookup-replicate : lookup i (replicate x) ≡ x
  lookup-⊛         : lookup i (fs ⊛ xs) ≡ (lookup i fs $ lookup i xs)
  tabulate-cong    : f ≗ g → tabulate f ≡ tabulate g
  ```

* Added new proofs to `Data.Vec.All.Properties`
  ```agda
  All-irrelevance : IrrelevantPred P → ∀ {n} → IrrelevantPred (All P {n})
  ```

* Added new proofs to `Data.Vec.Relation.Pointwise.Extensional`:
  ```agda
  isDecEquivalence      : IsDecEquivalence _~_ → IsDecEquivalence (Pointwise _~_)
  extensional⇒inductive : Pointwise _~_ xs ys → IPointwise _~_ xs ys
  inductive⇒extensional : IPointwise _~_ xs ys → Pointwise _~_ xs ys

  ≡⇒Pointwise-≡         : Pointwise _≡_ xs ys → xs ≡ ys
  Pointwise-≡⇒≡         : xs ≡ ys → Pointwise _≡_ xs ys
  ```

* Added new proofs to `Data.Vec.Relation.Pointwise.Inductive`:
  ```agda
  ++⁺              : Pointwise P xs → Pointwise P ys → Pointwise P (xs ++ ys)
  ++⁻ˡ             : Pointwise P (xs ++ ys) → Pointwise P xs
  ++⁻ʳ             : Pointwise P (xs ++ ys) → Pointwise P ys
  ++⁻              : Pointwise P (xs ++ ys) → Pointwise P xs × Pointwise P ys

  concat⁺          : Pointwise (Pointwise P) xss → Pointwise P (concat xss)
  concat⁻          : Pointwise P (concat xss) → Pointwise (Pointwise P) xss

  lookup           : Pointwise _~_ xs ys → ∀ i → lookup i xs ~ lookup i ys

  isDecEquivalence : IsDecEquivalence _~_ → IsDecEquivalence (Pointwise _~_)

  ≡⇒Pointwise-≡    : Pointwise _≡_ xs ys → xs ≡ ys
  Pointwise-≡⇒≡    : xs ≡ ys → Pointwise _≡_ xs ys

  Pointwiseˡ⇒All   : Pointwise (λ x y → P x) xs ys → All P xs
  Pointwiseʳ⇒All   : Pointwise (λ x y → P y) xs ys → All P ys
  All⇒Pointwiseˡ   : All P xs → Pointwise (λ x y → P x) xs ys
  All⇒Pointwiseʳ   : All P ys → Pointwise (λ x y → P y) xs ys
  ```

* Added new functions and proofs to `Data.W`:
  ```agda
  map            : (f : A → C) → ∀[ D ∘ f ⇒ B ] → W A B → W C D
  induction      : (∀ a {f} (hf : ∀ (b : B a) → P (f b)) → (w : W A B) → P w
  foldr          : (∀ a → (B a → P) → P) → W A B → P

  sup-injective₁ : sup x f ≡ sup y g → x ≡ y
  sup-injective₂ : sup x f ≡ sup x g → f ≡ g
  ```

* Added new properties to `Relation.Binary.PropositionalEquality`
  ```agda
  isPropositional A = (a b : A) → a ≡ b
  IrrelevantPred P  = ∀ {x} → isPropositional (P x)
  IrrelevantRel _~_ = ∀ {x y} → isPropositional (x ~ y)
  ```

* Added new combinator to ` Relation.Binary.PropositionalEquality.TrustMe`:
  ```agda
  postulate[_↦_] : (t : A) → B t → (x : A) → B x
  ```

* Added new proofs to `Relation.Binary.StrictToNonStrict`:
  ```agda
  isPreorder₁     : IsPreorder _≈_ _<_ → IsPreorder _≈_ _≤_
  isPreorder₂     : IsStrictPartialOrder _≈_ _<_ → IsPreorder _≈_ _≤_
  isPartialOrder  : IsStrictPartialOrder _≈_ _<_ → IsPartialOrder _≈_ _≤_
  isTotalOrder    : IsStrictTotalOrder _≈_ _<_ → IsTotalOrder _≈_ _≤_
  isDecTotalOrder : IsStrictTotalOrder _≈_ _<_ → IsDecTotalOrder _≈_ _≤_
  ```

* Added new syntax, relations and proofs to `Relation.Unary`:
  ```agda
  syntax Universal P = ∀[ P ]

  P ⊈  Q = ¬ (P ⊆ Q)
  P ⊉  Q = ¬ (P ⊇ Q)
  P ⊂  Q = P ⊆ Q × Q ⊈ P
  P ⊃  Q = Q ⊂ P
  P ⊄  Q = ¬ (P ⊂ Q)
  P ⊅  Q = ¬ (P ⊃ Q)
  P ⊈′ Q = ¬ (P ⊆′ Q)
  P ⊉′ Q = ¬ (P ⊇′ Q)
  P ⊂′ Q = P ⊆′ Q × Q ⊈′ P
  P ⊃′ Q = Q ⊂′ P
  P ⊄′ Q = ¬ (P ⊂′ Q)
  P ⊅′ Q = ¬ (P ⊃′ Q)

  f ⊢ P  = λ x → P (f x)

  ∁? : Decidable P → Decidable (∁ P)
  ```

* Added `recompute` to `Relation.Nullary`:
  ```agda
  recompute : ∀ {a} {A : Set a} → Dec A → .A → A
  ```

Version 0.14
============

The library has been tested using Agda version 2.5.3.

Non-backwards compatible changes
--------------------------------

#### 1st stage of overhaul of list membership

* The current setup for list membership is difficult to work with as both setoid membership
  and propositional membership exist as internal modules of `Data.Any`. Furthermore the
  top-level module `Data.List.Any.Membership` actually contains properties of propositional
  membership rather than the membership relation itself as its name would suggest.
  Consequently this leaves no place to reason about the properties of setoid membership.

  Therefore the two internal modules `Membership` and `Membership-≡` have been moved out
  of `Data.List.Any` into top-level `Data.List.Any.Membership` and
  `Data.List.Any.Membership.Propositional` respectively. The previous module
  `Data.List.Any.Membership` has been renamed
  `Data.List.Any.Membership.Propositional.Properties`.

  Accordingly some lemmas have been moved to more logical locations:
  - `lift-resp` has been moved from `Data.List.Any.Membership` to `Data.List.Any.Properties`
  - `∈-resp-≈`, `⊆-preorder` and `⊆-Reasoning` have been moved from `Data.List.Any.Membership`
  to `Data.List.Any.Membership.Properties`.
  - `∈-resp-list-≈` has been moved from `Data.List.Any.Membership` to
  `Data.List.Any.Membership.Properties` and renamed `∈-resp-≋`.
  - `swap` in `Data.List.Any.Properties` has been renamed `swap↔` and made more generic with
  respect to levels.

#### Moving `decTotalOrder` and `decSetoid` from `Data.X` to `Data.X.Properties`

* Currently the library does not directly expose proofs of basic properties such as reflexivity,
  transitivity etc. for `_≤_` in numeric datatypes such as `Nat`, `Integer` etc. In order to use these
  properties it was necessary to first import the `decTotalOrder` proof from `Data.X` and then
  separately open it, often having to rename the proofs as well. This adds unneccessary lines of
  code to the import statements for what are very commonly used properties.

  These basic proofs have now been added in `Data.X.Properties` along with proofs that they form
  pre-orders, partial orders and total orders. This should make them considerably easier to work with
  and simplify files' import preambles. However consequently the records `decTotalOrder` and
  `decSetoid` have been moved from `Data.X` to `≤-decTotalOrder` and `≡-decSetoid` in
  `Data.X.Properties`.

  The numeric datatypes for which this has been done are `Nat`, `Integer`, `Rational` and `Bin`.

  As a consequence the module `≤-Reasoning` has also had to have been moved from `Data.Nat` to
  `Data.Nat.Properties`.

#### New well-founded induction proofs for `Data.Nat`

* Currently `Induction.Nat` only proves that the non-standard `_<′_`relation over `ℕ` is
  well-founded. Unfortunately these existing proofs are named `<-Rec` and `<-well-founded`
  which clash with the sensible names for new proofs over the standard `_<_` relation.

  Therefore `<-Rec` and `<-well-founded` have been renamed to `<′-Rec` and `<′-well-founded`
  respectively. The original names `<-Rec` and `<-well-founded` now refer to new
  corresponding proofs for `_<_`.

#### Other

* Changed the implementation of `map` and `zipWith` in `Data.Vec` to use native
  (pattern-matching) definitions. Previously they were defined using the
  `applicative` operations of `Vec`. The new definitions can be converted back
  to the old using the new proofs `⊛-is-zipWith`, `map-is-⊛` and `zipWith-is-⊛`
  in `Data.Vec.Properties`. It has been argued that `zipWith` is fundamental than `_⊛_`
  and this change allows better printing of goals involving `map` or `zipWith`.

* Changed the implementation of `All₂` in `Data.Vec.All` to a native datatype. This
  improved improves pattern matching on terms and allows the new datatype to be more
  generic with respect to types and levels.

* Changed the implementation of `downFrom` in `Data.List` to a native
  (pattern-matching) definition. Previously it was defined using a private
  internal module which made pattern matching difficult.

* The arguments of `≤pred⇒≤` and `≤⇒pred≤` in `Data.Nat.Properties` are now implicit
  rather than explicit (was `∀ m n → m ≤ pred n → m ≤ n` and is now
  `∀ {m n} → m ≤ pred n → m ≤ n`). This makes it consistent with `<⇒≤pred` which
  already used implicit arguments, and shouldn't introduce any significant problems
  as both parameters can be inferred by Agda.

* Moved `¬∀⟶∃¬` from `Relation.Nullary.Negation` to `Data.Fin.Dec`. Its old
  location was causing dependency cyles to form between `Data.Fin.Dec`,
  `Relation.Nullary.Negation` and `Data.Fin`.

* Moved `fold`, `add` and `mul` from `Data.Nat` to new module `Data.Nat.GeneralisedArithmetic`.

* Changed type of second parameter of `Relation.Binary.StrictPartialOrderReasoning._<⟨_⟩_`
  from `x < y ⊎ x ≈ y` to `x < y`. `_≈⟨_⟩_` is left unchanged to take a value with type `x ≈ y`.
  Old code may be fixed by prefixing the contents of `_<⟨_⟩_` with `inj₁`.

Deprecated features
-------------------

Deprecated features still exist and therefore existing code should still work
but they may be removed in some future release of the library.

* The module `Data.Nat.Properties.Simple` is now deprecated. All proofs
  have been moved to `Data.Nat.Properties` where they should be used directly.
  The `Simple` file still exists for backwards compatability reasons and
  re-exports the proofs from `Data.Nat.Properties` but will be removed in some
  future release.

* The modules `Data.Integer.Addition.Properties` and
  `Data.Integer.Multiplication.Properties` are now deprecated. All proofs
  have been moved to `Data.Integer.Properties` where they should be used
  directly. The `Addition.Properties` and `Multiplication.Properties` files
  still exist for backwards compatability reasons and re-exports the proofs from
  `Data.Integer.Properties` but will be removed in some future release.

* The following renaming has occured in `Data.Nat.Properties`
  ```agda
  _+-mono_          ↦  +-mono-≤
  _*-mono_          ↦  *-mono-≤

  +-right-identity  ↦  +-identityʳ
  *-right-zero      ↦  *-zeroʳ
  distribʳ-*-+      ↦  *-distribʳ-+
  *-distrib-∸ʳ      ↦  *-distribʳ-∸
  cancel-+-left     ↦  +-cancelˡ-≡
  cancel-+-left-≤   ↦  +-cancelˡ-≤
  cancel-*-right    ↦  *-cancelʳ-≡
  cancel-*-right-≤  ↦  *-cancelʳ-≤

  strictTotalOrder                      ↦  <-strictTotalOrder
  isCommutativeSemiring                 ↦  *-+-isCommutativeSemiring
  commutativeSemiring                   ↦  *-+-commutativeSemiring
  isDistributiveLattice                 ↦  ⊓-⊔-isDistributiveLattice
  distributiveLattice                   ↦  ⊓-⊔-distributiveLattice
  ⊔-⊓-0-isSemiringWithoutOne            ↦  ⊔-⊓-isSemiringWithoutOne
  ⊔-⊓-0-isCommutativeSemiringWithoutOne ↦  ⊔-⊓-isCommutativeSemiringWithoutOne
  ⊔-⊓-0-commutativeSemiringWithoutOne   ↦  ⊔-⊓-commutativeSemiringWithoutOne
  ```

* The following renaming has occurred in `Data.Nat.Divisibility`:
  ```agda
  ∣-*   ↦   n|m*n
  ∣-+   ↦   ∣m∣n⇒∣m+n
  ∣-∸   ↦   ∣m+n|m⇒|n
  ```

Backwards compatible changes
----------------------------

* Added support for GHC 8.0.2 and 8.2.1.

* Removed the empty `Irrelevance` module

* Added `Category.Functor.Morphism` and module `Category.Functor.Identity`.

* `Data.Container` and `Data.Container.Indexed` now allow for different
  levels in the container and in the data it contains.

* Made `Data.BoundedVec` polymorphic with respect to levels.

* Access to `primForce` and `primForceLemma` has been provided via the new
  top-level module `Strict`.

* New call-by-value application combinator `_$!_` in `Function`.

* Added properties to `Algebra.FunctionProperties`:
  ```agda
  LeftCancellative  _•_ = ∀ x {y z} → (x • y) ≈ (x • z) → y ≈ z
  RightCancellative _•_ = ∀ {x} y z → (y • x) ≈ (z • x) → y ≈ z
  Cancellative      _•_ = LeftCancellative _•_ × RightCancellative _•_
  ```

* Added new module `Algebra.FunctionProperties.Consequences` for basic causal relationships between
  properties, containing:
  ```agda
  comm+idˡ⇒idʳ         : Commutative _•_ → LeftIdentity e _•_ → RightIdentity e _•_
  comm+idʳ⇒idˡ         : Commutative _•_ → RightIdentity e _•_ → LeftIdentity e _•_
  comm+zeˡ⇒zeʳ         : Commutative _•_ → LeftZero e _•_ → RightZero e _•_
  comm+zeʳ⇒zeˡ         : Commutative _•_ → RightZero e _•_ → LeftZero e _•_
  comm+invˡ⇒invʳ       : Commutative _•_ → LeftInverse e _⁻¹ _•_ → RightInverse e _⁻¹ _•_
  comm+invʳ⇒invˡ       : Commutative _•_ → RightInverse e _⁻¹ _•_ → LeftInverse e _⁻¹ _•_
  comm+distrˡ⇒distrʳ   : Commutative _•_ → _•_ DistributesOverˡ _◦_ → _•_ DistributesOverʳ _◦_
  comm+distrʳ⇒distrˡ   : Commutative _•_ → _•_ DistributesOverʳ _◦_ → _•_ DistributesOverˡ _◦_
  comm+cancelˡ⇒cancelʳ : Commutative _•_ → LeftCancellative _•_ → RightCancellative _•_
  comm+cancelˡ⇒cancelʳ : Commutative _•_ → LeftCancellative _•_ → RightCancellative _•_
  sel⇒idem           : Selective _•_ → Idempotent _•_
  ```

* Added proofs to `Algebra.Properties.BooleanAlgebra`:
  ```agda
  ∨-complementˡ : LeftInverse ⊤ ¬_ _∨_
  ∧-complementˡ : LeftInverse ⊥ ¬_ _∧_

  ∧-identityʳ   : RightIdentity ⊤ _∧_
  ∧-identityˡ   : LeftIdentity ⊤ _∧_
  ∧-identity    : Identity ⊤ _∧_

  ∨-identityʳ   : RightIdentity ⊥ _∨_
  ∨-identityˡ   : LeftIdentity ⊥ _∨_
  ∨-identity    : Identity ⊥ _∨_

  ∧-zeroʳ       : RightZero ⊥ _∧_
  ∧-zeroˡ       : LeftZero ⊥ _∧_
  ∧-zero        : Zero ⊥ _∧_

  ∨-zeroʳ       : RightZero ⊤ _∨_
  ∨-zeroˡ       : LeftZero ⊤ _∨_
  ∨-zero        : Zero ⊤ _∨_

  ⊕-identityˡ   : LeftIdentity ⊥ _⊕_
  ⊕-identityʳ   : RightIdentity ⊥ _⊕_
  ⊕-identity    : Identity ⊥ _⊕_

  ⊕-inverseˡ    : LeftInverse ⊥ id _⊕_
  ⊕-inverseʳ    : RightInverse ⊥ id _⊕_
  ⊕-inverse     : Inverse ⊥ id _⊕_

  ⊕-cong        : Congruent₂ _⊕_
  ⊕-comm        : Commutative _⊕_
  ⊕-assoc       : Associative _⊕_

  ∧-distribˡ-⊕  : _∧_ DistributesOverˡ _⊕_
  ∧-distribʳ-⊕  : _∧_ DistributesOverʳ _⊕_
  ∧-distrib-⊕   : _∧_ DistributesOver _⊕_

  ∨-isSemigroup           : IsSemigroup _≈_ _∨_
  ∧-isSemigroup           : IsSemigroup _≈_ _∧_
  ∨-⊥-isMonoid            : IsMonoid _≈_ _∨_ ⊥
  ∧-⊤-isMonoid            : IsMonoid _≈_ _∧_ ⊤
  ∨-⊥-isCommutativeMonoid : IsCommutativeMonoid _≈_ _∨_ ⊥
  ∧-⊤-isCommutativeMonoid : IsCommutativeMonoid _≈_ _∧_ ⊤

  ⊕-isSemigroup           : IsSemigroup _≈_ _⊕_
  ⊕-⊥-isMonoid            : IsMonoid _≈_ _⊕_ ⊥
  ⊕-⊥-isGroup             : IsGroup _≈_ _⊕_ ⊥ id
  ⊕-⊥-isAbelianGroup      : IsAbelianGroup _≈_ _⊕_ ⊥ id
  ⊕-∧-isRing              : IsRing _≈_ _⊕_ _∧_ id ⊥ ⊤
  ```

* Added proofs to `Algebra.Properties.DistributiveLattice`:
  ```agda
  ∨-∧-distribˡ : _∨_ DistributesOverˡ _∧_
  ∧-∨-distribˡ : _∧_ DistributesOverˡ _∨_
  ∧-∨-distribʳ : _∧_ DistributesOverʳ _∨_
  ```

* Added pattern synonyms to `Data.Bin` to improve readability:
  ```agda
  pattern 0b = zero
  pattern 1b = 1+ zero
  pattern ⊥b = 1+ 1+ ()
  ```

* A new module `Data.Bin.Properties` has been added, containing proofs:
  ```agda
  1#-injective         : as 1# ≡ bs 1# → as ≡ bs
  _≟_                  : Decidable {A = Bin} _≡_
  ≡-isDecEquivalence   : IsDecEquivalence _≡_
  ≡-decSetoid          : DecSetoid _ _

  <-trans              : Transitive _<_
  <-asym               : Asymmetric _<_
  <-irrefl             : Irreflexive _≡_ _<_
  <-cmp                : Trichotomous _≡_ _<_
  <-isStrictTotalOrder : IsStrictTotalOrder _≡_ _<_

  <⇒≢                  : a < b → a ≢ b
  1<[23]               : [] 1# < (b ∷ []) 1#
  1<2+                 : [] 1# < (b ∷ bs) 1#
  0<1+                 : 0# < bs 1#
  ```

* Added functions to `Data.BoundedVec`:
  ```agda
  toInefficient   : BoundedVec A n → Ineff.BoundedVec A n
  fromInefficient : Ineff.BoundedVec A n → BoundedVec A n
  ```

* Added the following to `Data.Digit`:
  ```agda
  Expansion : ℕ → Set
  Expansion base = List (Fin base)
  ```

* Added new module `Data.Empty.Irrelevant` containing an irrelevant version of `⊥-elim`.

* Added functions to `Data.Fin`:
  ```agda
  punchIn  i j ≈ if j≥i then j+1 else j
  punchOut i j ≈ if j>i then j-1 else j
  ```

* Added proofs to `Data.Fin.Properties`:
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
  punchInᵢ≢i           : punchIn i j ≢ i
  ```

* Added proofs to `Data.Fin.Subset.Properties`:
  ```agda
  x∈⁅x⁆     : x ∈ ⁅ x ⁆
  x∈⁅y⁆⇒x≡y : x ∈ ⁅ y ⁆ → x ≡ y

  ∪-assoc   : Associative _≡_ _∪_
  ∩-assoc   : Associative _≡_ _∩_
  ∪-comm    : Commutative _≡_ _∪_
  ∩-comm    : Commutative _≡_ _∩_

  p⊆p∪q     : p ⊆ p ∪ q
  q⊆p∪q     : q ⊆ p ∪ q
  x∈p∪q⁻    : x ∈ p ∪ q → x ∈ p ⊎ x ∈ q
  x∈p∪q⁺    : x ∈ p ⊎ x ∈ q → x ∈ p ∪ q

  p∩q⊆p     : p ∩ q ⊆ p
  p∩q⊆q     : p ∩ q ⊆ q
  x∈p∩q⁺    : x ∈ p × x ∈ q → x ∈ p ∩ q
  x∈p∩q⁻    : x ∈ p ∩ q → x ∈ p × x ∈ q
  ∩⇔×       : x ∈ p ∩ q ⇔ (x ∈ p × x ∈ q)
  ```

* Added relations to `Data.Integer`
  ```agda
  _≥_ : Rel ℤ _
  _<_ : Rel ℤ _
  _>_ : Rel ℤ _
  _≰_ : Rel ℤ _
  _≱_ : Rel ℤ _
  _≮_ : Rel ℤ _
  _≯_ : Rel ℤ _
  ```

* Added proofs to `Data.Integer.Properties`
  ```agda
  +-injective           : + m ≡ + n → m ≡ n
  -[1+-injective        : -[1+ m ] ≡ -[1+ n ] → m ≡ n

  doubleNeg             : - - n ≡ n
  neg-injective         : - m ≡ - n → m ≡ n

  ∣n∣≡0⇒n≡0             : ∣ n ∣ ≡ 0 → n ≡ + 0
  ∣-n∣≡∣n∣              : ∣ - n ∣ ≡ ∣ n ∣

  +◃n≡+n                : Sign.+ ◃ n ≡ + n
  -◃n≡-n                : Sign.- ◃ n ≡ - + n
  signₙ◃∣n∣≡n           : sign n ◃ ∣ n ∣ ≡ n
  ∣s◃m∣*∣t◃n∣≡m*n       : ∣ s ◃ m ∣ ℕ* ∣ t ◃ n ∣ ≡ m ℕ* n

  ⊖-≰                   : n ≰ m → m ⊖ n ≡ - + (n ∸ m)
  ∣⊖∣-≰                 : n ≰ m → ∣ m ⊖ n ∣ ≡ n ∸ m
  sign-⊖-≰              : n ≰ m → sign (m ⊖ n) ≡ Sign.-
  -[n⊖m]≡-m+n           : - (m ⊖ n) ≡ (- (+ m)) + (+ n)

  +-identity            : Identity (+ 0) _+_
  +-inverse             : Inverse (+ 0) -_ _+_
  +-0-isMonoid          : IsMonoid _≡_ _+_ (+ 0)
  +-0-isGroup           : IsGroup _≡_ _+_ (+ 0) (-_)
  +-0-abelianGroup      : AbelianGroup _ _

  n≢1+n                 : n ≢ suc n
  1-[1+n]≡-n            : suc -[1+ n ] ≡ - (+ n)
  neg-distrib-+         : - (m + n) ≡ (- m) + (- n)
  ◃-distrib-+           : s ◃ (m + n) ≡ (s ◃ m) + (s ◃ n)

  *-identityʳ           : RightIdentity (+ 1) _*_
  *-identity            : Identity (+ 1) _*_
  *-zeroˡ               : LeftZero (+ 0) _*_
  *-zeroʳ               : RightZero (+ 0) _*_
  *-zero                : Zero (+ 0) _*_
  *-1-isMonoid          : IsMonoid _≡_ _*_ (+ 1)
  -1*n≡-n               : -[1+ 0 ] * n ≡ - n
  ◃-distrib-*           : (s 𝕊* t) ◃ (m ℕ* n) ≡ (s ◃ m) * (t ◃ n)

  +-*-isRing            : IsRing _≡_ _+_ _*_ -_ (+ 0) (+ 1)
  +-*-isCommutativeRing : IsCommutativeRing _≡_ _+_ _*_ -_ (+ 0) (+ 1)

  ≤-reflexive           : _≡_ ⇒ _≤_
  ≤-refl                : Reflexive _≤_
  ≤-trans               : Transitive _≤_
  ≤-antisym             : Antisymmetric _≡_ _≤_
  ≤-total               : Total _≤_

  ≤-isPreorder          : IsPreorder _≡_ _≤_
  ≤-isPartialOrder      : IsPartialOrder _≡_ _≤_
  ≤-isTotalOrder        : IsTotalOrder _≡_ _≤_
  ≤-isDecTotalOrder     : IsDecTotalOrder _≡_ _≤_

  ≤-step                : n ≤ m → n ≤ suc m
  n≤1+n                 : n ≤ + 1 + n

  <-irrefl              : Irreflexive _≡_ _<_
  <-asym                : Asymmetric _<_
  <-trans               : Transitive _<_
  <-cmp                 : Trichotomous _≡_ _<_
  <-isStrictTotalOrder  : IsStrictTotalOrder _≡_ _<_

  n≮n                   : n ≮ n
  -<+                   : -[1+ m ] < + n
  <⇒≤                   : m < n → m ≤ n
  ≰→>                   : x ≰ y → x > y
  ```

* Added functions to `Data.List`
  ```agda
  applyUpTo f n     ≈ f[0]   ∷ f[1]   ∷ ... ∷ f[n-1] ∷ []
  upTo n            ≈ 0      ∷ 1      ∷ ... ∷ n-1    ∷ []
  applyDownFrom f n ≈ f[n-1] ∷ f[n-2] ∷ ... ∷ f[0]   ∷ []
  tabulate f        ≈ f[0]   ∷ f[1]   ∷ ... ∷ f[n-1] ∷ []
  allFin n          ≈ 0f     ∷ 1f     ∷ ... ∷ n-1f   ∷ []
  ```

* Added proofs to `Data.List.Properties`
  ```agda
  map-id₂        : All (λ x → f x ≡ x) xs → map f xs ≡ xs
  map-cong₂      : All (λ x → f x ≡ g x) xs → map f xs ≡ map g xs
  foldr-++       : foldr f x (ys ++ zs) ≡ foldr f (foldr f x zs) ys
  foldl-++       : foldl f x (ys ++ zs) ≡ foldl f (foldl f x ys) zs
  foldr-∷ʳ       : foldr f x (ys ∷ʳ y) ≡ foldr f (f y x) ys
  foldl-∷ʳ       : foldl f x (ys ∷ʳ y) ≡ f (foldl f x ys) y
  reverse-foldr  : foldr f x (reverse ys) ≡ foldl (flip f) x ys
  reverse-foldr  : foldl f x (reverse ys) ≡ foldr (flip f) x ys
  length-reverse : length (reverse xs) ≡ length xs
  ```

* Added proofs to `Data.List.All.Properties`
  ```agda
  All-universal : Universal P → All P xs

  ¬Any⇒All¬     : ¬ Any P xs → All (¬_ ∘ P) xs
  All¬⇒¬Any     : All (¬_ ∘ P) xs → ¬ Any P xs
  ¬All⇒Any¬     : Decidable P → ¬ All P xs → Any (¬_ ∘ P) xs

  ++⁺           : All P xs → All P ys → All P (xs ++ ys)
  ++⁻ˡ          : All P (xs ++ ys) → All P xs
  ++⁻ʳ          : All P (xs ++ ys) → All P ys
  ++⁻           : All P (xs ++ ys) → All P xs × All P ys

  concat⁺       : All (All P) xss → All P (concat xss)
  concat⁻       : All P (concat xss) → All (All P) xss

  drop⁺         : All P xs → All P (drop n xs)
  take⁺         : All P xs → All P (take n xs)

  tabulate⁺     : (∀ i → P (f i)) → All P (tabulate f)
  tabulate⁻     : All P (tabulate f) → (∀ i → P (f i))

  applyUpTo⁺₁   : (∀ {i} → i < n → P (f i)) → All P (applyUpTo f n)
  applyUpTo⁺₂   : (∀ i → P (f i)) → All P (applyUpTo f n)
  applyUpTo⁻    : All P (applyUpTo f n) → ∀ {i} → i < n → P (f i)
  ```

* Added proofs to `Data.List.Any.Properties`
  ```agda
  lose∘find   : uncurry′ lose (proj₂ (find p)) ≡ p
  find∘lose   : find (lose x∈xs pp) ≡ (x , x∈xs , pp)

  swap        : Any (λ x → Any (P x) ys) xs → Any (λ y → Any (flip P y) xs) ys
  swap-invol  : swap (swap any) ≡ any

  ∃∈-Any      : (∃ λ x → x ∈ xs × P x) → Any P xs

  Any-⊎⁺      : Any P xs ⊎ Any Q xs → Any (λ x → P x ⊎ Q x) xs
  Any-⊎⁻      : Any (λ x → P x ⊎ Q x) xs → Any P xs ⊎ Any Q xs
  Any-×⁺      : Any P xs × Any Q ys → Any (λ x → Any (λ y → P x × Q y) ys) xs
  Any-×⁻      : Any (λ x → Any (λ y → P x × Q y) ys) xs → Any P xs × Any Q ys

  map⁺        : Any (P ∘ f) xs → Any P (map f xs)
  map⁻        : Any P (map f xs) → Any (P ∘ f) xs

  ++⁺ˡ        : Any P xs → Any P (xs ++ ys)
  ++⁺ʳ        : Any P ys → Any P (xs ++ ys)
  ++⁻         : Any P (xs ++ ys) → Any P xs ⊎ Any P ys

  concat⁺     : Any (Any P) xss → Any P (concat xss)
  concat⁻     : Any P (concat xss) → Any (Any P) xss

  applyUpTo⁺  : P (f i) → i < n → Any P (applyUpTo f n)
  applyUpTo⁻  : Any P (applyUpTo f n) → ∃ λ i → i < n × P (f i)

  tabulate⁺   : P (f i) → Any P (tabulate f)
  tabulate⁻   : Any P (tabulate f) → ∃ λ i → P (f i)

  map-with-∈⁺ : (∃₂ λ x (x∈xs : x ∈ xs) → P (f x∈xs)) → Any P (map-with-∈ xs f)
  map-with-∈⁻ : Any P (map-with-∈ xs f) → ∃₂ λ x (x∈xs : x ∈ xs) → P (f x∈xs)

  return⁺     : P x → Any P (return x)
  return⁻     : Any P (return x) → P x
  ```

* Added proofs to `Data.List.Any.Membership.Properties`
  ```agda
  ∈-map⁺ :  x ∈ xs → f x ∈ map f xs
  ∈-map⁻ :  y ∈ map f xs → ∃ λ x → x ∈ xs × y ≈ f x
  ```

* Added proofs to `Data.List.Any.Membership.Propositional.Properties`
  ```agda
  ∈-map⁺ :  x ∈ xs → f x ∈ map f xs
  ∈-map⁻ :  y ∈ map f xs → ∃ λ x → x ∈ xs × y ≈ f x
  ```

* Added proofs to `Data.Maybe`:
  ```agda
  Eq-refl             : Reflexive _≈_ → Reflexive (Eq _≈_)
  Eq-sym              : Symmetric _≈_ → Symmetric (Eq _≈_)
  Eq-trans            : Transitive _≈_ → Transitive (Eq _≈_)
  Eq-dec              : Decidable _≈_ → Decidable (Eq _≈_)
  Eq-isEquivalence    : IsEquivalence _≈_ → IsEquivalence (Eq _≈_)
  Eq-isDecEquivalence : IsDecEquivalence _≈_ → IsDecEquivalence (Eq _≈_)
  ```

* Added exponentiation operator `_^_` to `Data.Nat.Base`

* Added proofs to `Data.Nat.Properties`:
  ```agda
  suc-injective         : suc m ≡ suc n → m ≡ n
  ≡-isDecEquivalence    : IsDecEquivalence (_≡_ {A = ℕ})
  ≡-decSetoid           : DecSetoid _ _

  ≤-reflexive           : _≡_ ⇒ _≤_
  ≤-refl                : Reflexive _≤_
  ≤-trans               : Antisymmetric _≡_ _≤_
  ≤-antisymmetric       : Transitive _≤_
  ≤-total               : Total _≤_
  ≤-isPreorder          : IsPreorder _≡_ _≤_
  ≤-isPartialOrder      : IsPartialOrder _≡_ _≤_
  ≤-isTotalOrder        : IsTotalOrder _≡_ _≤_
  ≤-isDecTotalOrder     : IsDecTotalOrder _≡_ _≤_

  _<?_                  : Decidable _<_
  <-irrefl              : Irreflexive _≡_ _<_
  <-asym                : Asymmetric _<_
  <-transʳ              : Trans _≤_ _<_ _<_
  <-transˡ              : Trans _<_ _≤_ _<_
  <-isStrictTotalOrder  : IsStrictTotalOrder _≡_ _<_
  <⇒≤                   : _<_ ⇒ _≤_
  <⇒≢                   : _<_ ⇒ _≢_
  <⇒≱                   : _<_ ⇒ _≱_
  <⇒≯                   : _<_ ⇒ _≯_
  ≰⇒≮                   : _≰_ ⇒ _≮_
  ≰⇒≥                   : _≰_ ⇒ _≥_
  ≮⇒≥                   : _≮_ ⇒ _≥_
  ≤+≢⇒<                 : m ≤ n → m ≢ n → m < n

  +-identityˡ           : LeftIdentity 0 _+_
  +-identity            : Identity 0 _+_
  +-cancelʳ-≡           : RightCancellative _≡_ _+_
  +-cancel-≡            : Cancellative _≡_ _+_
  +-cancelʳ-≤           : RightCancellative _≤_ _+_
  +-cancel-≤            : Cancellative _≤_ _+_
  +-isSemigroup         : IsSemigroup _≡_ _+_
  +-monoˡ-<             : _+_ Preserves₂ _<_ ⟶ _≤_ ⟶ _<_
  +-monoʳ-<             : _+_ Preserves₂ _≤_ ⟶ _<_ ⟶ _<_
  +-mono-<              : _+_ Preserves₂ _<_ ⟶ _<_ ⟶ _<_
  m+n≤o⇒m≤o             : m + n ≤ o → m ≤ o
  m+n≤o⇒n≤o             : m + n ≤ o → n ≤ o
  m+n≮n                 : m + n ≮ n

  *-zeroˡ               : LeftZero 0 _*_
  *-zero                : Zero 0 _*_
  *-identityˡ           : LeftIdentity 1 _*_
  *-identityʳ           : RightIdentity 1 _*_
  *-identity            : Identity 1 _*_
  *-distribˡ-+          : _*_ DistributesOverˡ _+_
  *-distrib-+           : _*_ DistributesOver _+_
  *-isSemigroup         : IsSemigroup _≡_ _*_
  *-mono-<              : _*_ Preserves₂ _<_ ⟶ _<_ ⟶ _<_
  *-monoˡ-<             : (_* suc n) Preserves _<_ ⟶ _<_
  *-monoʳ-<             : (suc n *_) Preserves _<_ ⟶ _<_
  *-cancelˡ-≡           : suc k * i ≡ suc k * j → i ≡ j

  ^-distribˡ-+-*        : m ^ (n + p) ≡ m ^ n * m ^ p
  i^j≡0⇒i≡0             : i ^ j ≡ 0 → i ≡ 0
  i^j≡1⇒j≡0∨i≡1         : i ^ j ≡ 1 → j ≡ 0 ⊎ i ≡ 1

  ⊔-assoc               : Associative _⊔_
  ⊔-comm                : Commutative _⊔_
  ⊔-idem                : Idempotent _⊔_
  ⊔-identityˡ           : LeftIdentity 0 _⊔_
  ⊔-identityʳ           : RightIdentity 0 _⊔_
  ⊔-identity            : Identity 0 _⊔_
  ⊓-assoc               : Associative _⊓_
  ⊓-comm                : Commutative _⊓_
  ⊓-idem                : Idempotent _⊓_
  ⊓-zeroˡ               : LeftZero 0 _⊓_
  ⊓-zeroʳ               : RightZero 0 _⊓_
  ⊓-zero                : Zero 0 _⊓_
  ⊓-distribʳ-⊔          : _⊓_ DistributesOverʳ _⊔_
  ⊓-distribˡ-⊔          : _⊓_ DistributesOverˡ _⊔_
  ⊔-abs-⊓               : _⊔_ Absorbs _⊓_
  ⊓-abs-⊔               : _⊓_ Absorbs _⊔_
  m⊓n≤n                 : m ⊓ n ≤ n
  m≤m⊔n                 : m ≤ m ⊔ n
  m⊔n≤m+n               : m ⊔ n ≤ m + n
  m⊓n≤m+n               : m ⊓ n ≤ m + n
  m⊓n≤m⊔n               : m ⊔ n ≤ m ⊔ n
  ⊔-mono-≤              : _⊔_ Preserves₂ _≤_ ⟶ _≤_ ⟶ _≤_
  ⊔-mono-<              : _⊔_ Preserves₂ _<_ ⟶ _<_ ⟶ _<_
  ⊓-mono-≤              : _⊓_ Preserves₂ _≤_ ⟶ _≤_ ⟶ _≤_
  ⊓-mono-<              : _⊓_ Preserves₂ _<_ ⟶ _<_ ⟶ _<_
  +-distribˡ-⊔          : _+_ DistributesOverˡ _⊔_
  +-distribʳ-⊔          : _+_ DistributesOverʳ _⊔_
  +-distrib-⊔           : _+_ DistributesOver _⊔_
  +-distribˡ-⊓          : _+_ DistributesOverˡ _⊓_
  +-distribʳ-⊓          : _+_ DistributesOverʳ _⊓_
  +-distrib-⊓           : _+_ DistributesOver _⊓_
  ⊔-isSemigroup         : IsSemigroup _≡_ _⊔_
  ⊓-isSemigroup         : IsSemigroup _≡_ _⊓_
  ⊓-⊔-isLattice         : IsLattice _≡_ _⊓_ _⊔_

  ∸-distribʳ-⊔          : _∸_ DistributesOverʳ _⊔_
  ∸-distribʳ-⊓          : _∸_ DistributesOverʳ _⊓_
  +-∸-comm              : o ≤ m → (m + n) ∸ o ≡ (m ∸ o) + n
  ```

* Added decidability relation to `Data.Nat.GCD`
  ```agda
  gcd? : (m n d : ℕ) → Dec (GCD m n d)
  ```

* Added "not-divisible-by" relation to `Data.Nat.Divisibility`
  ```agda
  m ∤ n = ¬ (m ∣ n)
  ```

* Added proofs to `Data.Nat.Divisibility`
  ```agda
  ∣-reflexive      : _≡_ ⇒ _∣_
  ∣-refl           : Reflexive _∣_
  ∣-trans          : Transitive _∣_
  ∣-antisym        : Antisymmetric _≡_ _∣_
  ∣-isPreorder     : IsPreorder _≡_ _∣_
  ∣-isPartialOrder : IsPartialOrder _≡_ _∣_

  n∣n              : n ∣ n
  ∣m∸n∣n⇒∣m        : n ≤ m → i ∣ m ∸ n → i ∣ n → i ∣ m
  ```

* Added proofs to `Data.Nat.GeneralisedArithmetic`:
  ```agda
  fold-+     : fold z s (m + n) ≡ fold (fold z s n) s m
  fold-k     : fold k (s ∘′_) m z ≡ fold (k z) s m
  fold-*     : fold z s (m * n) ≡ fold z (fold id (s ∘_) n) m
  fold-pull  : fold p s m ≡ g (fold z s m) p

  id-is-fold : fold zero suc m ≡ m
  +-is-fold  : fold n suc m ≡ m + n
  *-is-fold  : fold zero (n +_) m ≡ m * n
  ^-is-fold  : fold 1 (m *_) n ≡ m ^ n
  *+-is-fold : fold p (n +_) m ≡ m * n + p
  ^*-is-fold : fold p (m *_) n ≡ m ^ n * p
  ```

* Added syntax for existential quantifiers in `Data.Product`:
  ```agda
  ∃-syntax (λ x → B) = ∃[ x ] B
  ∄-syntax (λ x → B) = ∄[ x ] B
  ```

* A new module `Data.Rational.Properties` has been added, containing proofs:
  ```agda
  ≤-reflexive : _≡_ ⇒ _≤_
  ≤-refl      : Reflexive _≤_
  ≤-trans     : Transitive _≤_
  ≤-antisym   : Antisymmetric _≡_ _≤_
  ≤-total     : Total _≤_

  ≤-isPreorder : IsPreorder _≡_ _≤_
  ≤-isPartialOrder : IsPartialOrder _≡_ _≤_
  ≤-isTotalOrder : IsTotalOrder _≡_ _≤_
  ≤-isDecTotalOrder : IsDecTotalOrder _≡_ _≤_
  ```

* Added proofs to `Data.Sign.Properties`:
  ```agda
  opposite-cong  : opposite s ≡ opposite t → s ≡ t

  *-identityˡ    : LeftIdentity + _*_
  *-identityʳ    : RightIdentity + _*_
  *-identity     : Identity + _*_
  *-comm         : Commutative _*_
  *-assoc        : Associative _*_
  cancel-*-left  : LeftCancellative _*_
  *-cancellative : Cancellative _*_
  s*s≡+          : s * s ≡ +
  ```

* Added definitions to `Data.Sum`:
  ```agda
  From-inj₁ : ∀ {a b} {A : Set a} {B : Set b} → A ⊎ B → Set a
  from-inj₁ : ∀ {a b} {A : Set a} {B : Set b} (x : A ⊎ B) → From-inj₁ x
  From-inj₂ : ∀ {a b} {A : Set a} {B : Set b} → A ⊎ B → Set b
  from-inj₂ : ∀ {a b} {A : Set a} {B : Set b} (x : A ⊎ B) → From-inj₂ x
  ```

* Added a functor encapsulating `map` in `Data.Vec`:
  ```agda
  functor = record { _<$>_ = map}
  ```

* Added proofs to `Data.Vec.Equality`
  ```agda
  to-≅      : xs ≈ ys → xs ≅ ys
  xs++[]≈xs  : xs ++ [] ≈ xs
  xs++[]≅xs : xs ++ [] ≅ xs
  ```

* Added proofs to `Data.Vec.Properties`
  ```agda
  lookup-map              : lookup i (map f xs) ≡ f (lookup i xs)
  lookup-functor-morphism : Morphism functor IdentityFunctor
  map-replicate           : map f (replicate x) ≡ replicate (f x)

  ⊛-is-zipWith            : fs ⊛ xs ≡ zipWith _$_ fs xs
  map-is-⊛                : map f xs ≡ replicate f ⊛ xs
  zipWith-is-⊛            : zipWith f xs ys ≡ replicate f ⊛ xs ⊛ ys

  zipWith-replicate₁      : zipWith _⊕_ (replicate x) ys ≡ map (x ⊕_) ys
  zipWith-replicate₂      : zipWith _⊕_ xs (replicate y) ≡ map (_⊕ y) xs
  zipWith-map₁            : zipWith _⊕_ (map f xs) ys ≡ zipWith (λ x y → f x ⊕ y) xs ys
  zipWith-map₂            : zipWith _⊕_ xs (map f ys) ≡ zipWith (λ x y → x ⊕ f y) xs ys
  ```

* Added proofs to `Data.Vec.All.Properties`
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

* Added non-dependant versions of the application combinators in `Function` for use
  cases where the most general one leads to unsolved meta variables:
  ```agda
  _$′_  : (A → B) → (A → B)
  _$!′_ : (A → B) → (A → B)
  ```

* Added proofs to `Relation.Binary.Consequences`
  ```agda
  P-resp⟶¬P-resp : Symmetric _≈_ → P Respects _≈_ → (¬_ ∘ P) Respects _≈_
  ```

* Added conversion lemmas to `Relation.Binary.HeterogeneousEquality`
  ```agda
  ≅-to-type-≡  : {x : A} {y : B} → x ≅ y → A ≡ B
  ≅-to-subst-≡ : (p : x ≅ y) → subst (λ x → x) (≅-to-type-≡ p) x ≡ y
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
  `Category.Monad.Partiality.All._⟨_⟩P`, was changed from `infix 2` to
  `infix 3`.

* The fixity of `Category.Monad.Partiality._≟-Kind_`, `Data.AVL._∈?_`,
  `Data.AVL.IndexedMap._∈?_`, `Data.AVL.Sets._∈?_`, `Data.Bool._≟_`,
  `Data.Char._≟_`, `Data.Float._≟_`, `Data.Nat._≤?_`,
  `Data.Nat.Divisibility._∣?_`, `Data.Sign._≟_`, `Data.String._≟_`,
  `Data.Unit._≟_`, `Data.Unit._≤?_` and
  `Data.Vec.Equality.DecidableEquality._≟_` was changed from the
  default to `infix 4`.

* The fixity of all `_≟<something>_` operators in `Reflection` is now
  `infix 4` (some of them already had this fixity).

* The fixity of `Algebra.Operations._×′_` was changed from the default
  to `infixr 7`.

* The fixity of `Data.Fin.#_` was changed from the default to
  `infix 10`.

* The fixity of `Data.Nat.Divisibility.1∣_` and `_∣0` was changed from
  the default to `infix 10`.

* The fixity of `Data.Nat.DivMod._divMod_`, `_div_` and `_mod_` was
  changed from the default to `infixl 7`.

* The fixity of `Data.Product.Σ-syntax` was changed from the default
  to `infix 2`.

* The fixity of `Relation.Unary._~` was changed from the default to
  `infix 10`.

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
    Issue [#1207](https://github.com/agda/agda/issues/1269)).

  + The `Reflection.type` function returns a normalised
    `Reflection.Type` and `quoteTerm` returns an η-contracted
    `Reflection.Term` now. These changes could break some code (see
    Agda Issue [#1269](https://github.com/agda/agda/issues/1269)).

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

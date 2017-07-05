Version TODO
============

The library has been tested using Agda version TODO.

Important changes since 0.13:

Non-backwards compatible changes
--------------------------------

* Added new module `Data.Bin.Properties` and moved `strictTotalOrder` and
  `decSetoid` from `Data.Bin` to `<-strictTotalOrder` and `≡-decSetoid`
  in `Data.Bin.Properties`.

  Reasons:

  1. `Data.Bin` was becoming too large.
  2. Better conforms to library conventions for other numeric datatypes.

* Moved `decTotalOrder` in `Data.Nat` to `≤-decTotalOrder` in
  `Data.Nat.Properties`.

  Reasons:

  1. Its old location was causing dependency cyles when trying to add new ordering
         properties to `Data.Nat.Properties`.
  2. Better conforms to library conventions.

* Moved module `≤-Reasoning` from `Data.Nat` to `Data.Nat.Properties`

* Moved `¬∀⟶∃¬` from `Relation.Nullary.Negation` to `Data.Fin.Dec`.

  Reasons:

  1. Its old location was causing dependency cyles to form between `Data.Fin.Dec`,
         `Relation.Nullary.Negation` and `Data.Fin`.

* Moved existing contents of `Data.List.Any.Membership` to
  `Data.List.Any.Membership.Propositional.Properties` and moved internal modules
  `Membership` and `Membership-≡` out of `Data.List.Any` into
  `Data.List.Any.Membership` and `Data.List.Any.Membership.Propositional`
  respectively.

  Reasons:

  1. Improves the ease of importing and opening the membership modules.
  2. Allows the creation of a new file `Data.List.Any.Membership.Properties`
     for setoid membership properties.

* The well-founded relation proofs for the `_<′_` relation have been renamed
  from `<-Rec` and `<-well-founded` to `<′-Rec` and `<′-well-founded`
  respectively. The original names `<-Rec` and `<-well-founded` now refer to new
  corresponding proofs for `_<_`.

  Reasons:

  1. The old names were confusing for newcomers to the library as they
     would assume `<-wellfounded` referred to the standard `_<_` relation.
  2. Without renaming the existing proofs, there was no way of adding
     wellfoundedness proofs for the `_<_` relation without increasing the
     confusion.

* Changed the implementation of `map` and `zipWith` in `Data.Vec` to use native
  (pattern-matching) definitions. Previously they were defined using the
  `applicative` operations of `Vec`. The new definitions can be converted back
  to the old using the new proofs `⊛-is-zipWith`, `map-is-⊛` and `zipWith-is-⊛`
  in `Data.Vec.Properties`.

  Reasons:

  1. Better printing of goals involving `map` or `zipWith`.
  2. It has been argued that `zipWith` is fundamental than `_⊛_`.

* Changed the implementation of `All₂` in `Data.Vec.All` to a native datatype.

  Reasons:

  1. Improves pattern matching on terms.
  2. The new datatype is more generic with respect to types and levels.

* Changed the implementation of `downFrom` in `Data.List` to a native
  (pattern-matching) definition. Previously it was defined using a private
  internal module.

  Reasons:

  1.  Improves pattern matching on terms.

Deprecated features
-------------------

Deprecated features still exist and therefore existing code should still work
but they may be removed in some future release of the library.

* The infix versions of `_+-mono_` and `_*-mono_` in `Data.Nat.Properties`
  have been deprecated in favour of `+-mono-≤` and `*-mono-≤` which better
  follow the library's naming conventions.

* The module `Data.Nat.Properties.Simple` is now deprecated. All proofs
  have been moved to `Data.Nat.Properties` where they should be used directly.
  The `Simple` file still exists for backwards compatability reasons and
  re-exports the proofs from `Data.Nat.Properties` but will be removed in some
  future release.

* The module `Data.Integer.Addition.Properties` is now deprecated. All proofs
  have been moved to `Data.Integer.Properties` where they should be used
  directly. The `Addition.Properties` file still exists for backwards
  compatability reasons and re-exports the proofs from `Data.Integer.Properties`
  but will be removed in some future release.

* The module `Data.Integer.Multiplication.Properties` is now deprecated. All
  proofs have been moved to `Data.Integer.Properties` where they should be used
  directly. The `Multiplication.Properties` file still exists for backwards
  compatability reasons and re-exports the proofs from `Data.Integer.Properties`
  but will be removed in some future release.

Backwards compatible changes
----------------------------

* Added support for GHC 8.0.2.

* Removed the empty `Irrelevance` module

* Added `Category.Functor.Morphism` and module `Category.Functor.Identity`.

* `Data.Container` and `Data.Container.Indexed` now allow for different
  levels in the container and in the data it contains.

* Added new module `Data.Empty.Irrelevant` containing an irrelevant version of
  `⊥-elim`.

* Added syntax for existential quantifiers in `Data.Product`:
  ```agda
  ∃-syntax (λ x → B) = ∃[ x ] B
  ∄-syntax (λ x → B) = ∄[ x ] B
  ```

* Added properties to `Algebra.FunctionProperties`:
  ```agda
  LeftCancellative  _•_ = ∀ x {y z} → (x • y) ≈ (x • z) → y ≈ z
  RightCancellative _•_ = ∀ {x} y z → (y • x) ≈ (z • x) → y ≈ z
  Cancellative      _•_ = LeftCancellative _•_ × RightCancellative _•_
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

  ∨-zeroʳ       : ∀ x → x ∨ ⊤ ≈ ⊤
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

* Added proofs to `Data.Bin.Properties`:
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
  x∈⁅x⁆     : ∀ {n} (x : Fin n) → x ∈ ⁅ x ⁆
  x∈⁅y⁆⇒x≡y : ∀ {n x} (y : Fin n) → x ∈ ⁅ y ⁆ → x ≡ y

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

  ∣n∣≡0⇒n≡0             : ∀ {n} → ∣ n ∣ ≡ 0 → n ≡ + 0
  ∣-n∣≡∣n∣              : ∀ n → ∣ - n ∣ ≡ ∣ n ∣

  +◃n≡+n                : Sign.+ ◃ n ≡ + n
  -◃n≡-n                : Sign.- ◃ n ≡ - + n
  signₙ◃∣n∣≡n           : sign n ◃ ∣ n ∣ ≡ n
  ∣s◃m∣*∣t◃n∣≡m*n          : ∀ s t m n → ∣ s ◃ m ∣ ℕ* ∣ t ◃ n ∣ ≡ m ℕ* n

  ⊖-≰                   : n ≰ m → m ⊖ n ≡ - + (n ∸ m)
  ∣⊖∣-≰                 : n ≰ m → ∣ m ⊖ n ∣ ≡ n ∸ m
  sign-⊖-≰              : n ≰ m → sign (m ⊖ n) ≡ Sign.-
  -[n⊖m]≡-m+n           : - (m ⊖ n) ≡ (- (+ m)) + (+ n)

  +-identity            : Identity (+ 0) _+_
  +-inverse             : Inverse (+ 0) -_ _+_
  +-0-isMonoid          : IsMonoid _≡_ _+_ (+ 0)
  +-0-isGroup           : IsGroup _≡_ _+_ (+ 0) (-_)
  +-0-abelianGroup      : AbelianGroup _ _
  neg-distrib-+         : - (m + n) ≡ (- m) + (- n)
  ◃-distrib-+           : s ◃ (m + n) ≡ (s ◃ m) + (s ◃ n)

  *-identityʳ           : RightIdentity (+ 1) _*_
  *-identity            : Identity (+ 1) _*_
  *-zeroˡ               : LeftZero (+ 0) _*_
  *-zeroʳ               : RightZero (+ 0) _*_
  *-zero                : Zero (+ 0) _*_
  *-1-isMonoid          : IsMonoid _≡_ _*_ (+ 1)
  -1*n≡-n               : -[1+ 0 ] * n ≡ - n
  ◃-distrib-*           :  ∀ s t m n → (s 𝕊* t) ◃ (m ℕ* n) ≡ (s ◃ m) * (t ◃ n)

  +-*-isRing            : IsRing _≡_ _+_ _*_ -_ (+ 0) (+ 1)
  +-*-isCommutativeRing : IsCommutativeRing _≡_ _+_ _*_ -_ (+ 0) (+ 1)
  ```

* Added proofs to `Data.Nat.Properties`:
  ```agda
  suc-injective        : suc m ≡ suc n → m ≡ n
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
  <⇒≤                  : _<_ ⇒ _≤_
  <⇒≢                  : _<_ ⇒ _≢_
  <⇒≱                  : _<_ ⇒ _≱_
  <⇒≯                  : _<_ ⇒ _≯_
  ≰⇒≮                  : _≰_ ⇒ _≮_
  ≰⇒≥                  : _≰_ ⇒ _≥_
  ≮⇒≥                  : _≮_ ⇒ _≥_
  ≤+≢⇒<                : m ≤ n → m ≢ n → m < n

  +-left-identity      : LeftIdentity 0 _+_
  +-identity           : Identity 0 _+_
  cancel-+-right       : RightCancellative _+_
  +-cancellative       : Cancellative _+_
  +-isSemigroup        : IsSemigroup _≡_ _+_
  +-monoˡ-<            : _+_ Preserves₂ _<_ ⟶ _≤_ ⟶ _<_
  +-monoʳ-<            : _+_ Preserves₂ _≤_ ⟶ _<_ ⟶ _<_
  +-mono-<             : _+_ Preserves₂ _<_ ⟶ _<_ ⟶ _<_

  *-left-zero          : LeftZero 0 _*_
  *-zero               : Zero 0 _*_
  *-left-identity      : LeftIdentity 1 _*_
  *-right-identity     : RightIdentity 1 _*_
  *-identity           : Identity 1 _*_
  distribˡ-*-+         : _*_ DistributesOverˡ _+_
  distrib-*-+          : _*_ DistributesOver _+_
  *-isSemigroup        : IsSemigroup _≡_ _*_
  *-mono-<             : _*_ Preserves₂ _<_ ⟶ _<_ ⟶ _<_
  *-monoˡ-<            : (_* suc n) Preserves _<_ ⟶ _<_
  *-monoʳ-<            : (suc n *_) Preserves _<_ ⟶ _<_

  ⊓-idem               : Idempotent _⊓_
  ⊔-idem               : Idempotent _⊔_
  m⊓n≤n                : m ⊓ n ≤ n
  m≤m⊔n                : m ≤ m ⊔ n
  m⊔n≤m+n              : m ⊔ n ≤ m + n
  m⊓n≤m+n              : m ⊓ n ≤ m + n
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

* Added proofs to `Data.Nat.Divisibility`
  ```agda
  ∣-reflexive      : _≡_ ⇒ _∣_
  ∣-refl           : Reflexive _∣_
  ∣-trans          : Transitive _∣_
  ∣-antisym        : Antisymmetric _≡_ _∣_
  ∣-isPreorder     : IsPreorder _≡_ _∣_
  ∣-isPartialOrder : IsPartialOrder _≡_ _∣_
  ```

* Added proofs to `Data.List.Properties`
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

* Added functions to `Data.List`
  ```agda
  applyUpTo f n     ≈ f[0]   ∷ f[1]   ∷ ... ∷ f[n-1] ∷ []
  upTo n            ≈ 0      ∷ 1      ∷ ... ∷ n-1    ∷ []
  applyDownFrom f n ≈ f[n-1] ∷ f[n-2] ∷ ... ∷ f[0]   ∷ []
  tabulate f        ≈ f[0]   ∷ f[1]   ∷ ... ∷ f[n-1] ∷ []
  allFin n          ≈ 0f     ∷ 1f     ∷ ... ∷ n-1f   ∷ []
  ```

* Added proofs to `Data.List.Any.Properties`
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

* Added a functor encapsulating `map` in `Data.Vec`:
  ```agda
  functor = record { _<$>_ = map}
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

* Added proofs to `Relation.Binary.Consequences`
  ```agda
  P-resp⟶¬P-resp : Symmetric _≈_ → P Respects _≈_ → (¬_ ∘ P) Respects _≈_
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

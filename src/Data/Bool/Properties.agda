------------------------------------------------------------------------
-- The Agda standard library
--
-- A bunch of properties
------------------------------------------------------------------------

module Data.Bool.Properties where

open import Data.Bool
open import Function
open import Function.Equality using (_⟨$⟩_)
open import Function.Equivalence
  using (_⇔_; equivalence; module Equivalence)
open import Algebra
open import Algebra.Structures
import Algebra.RingSolver.Simple as Solver
import Algebra.RingSolver.AlmostCommutativeRing as ACR
open import Relation.Binary.PropositionalEquality
  hiding ([_]; proof-irrelevance)
open ≡-Reasoning
open import Algebra.FunctionProperties (_≡_ {A = Bool})
open import Data.Product
open import Data.Sum
open import Data.Empty

------------------------------------------------------------------------
-- Properties of _∨_

∨-assoc : Associative _∨_
∨-assoc true  y z = refl
∨-assoc false y z = refl

∨-comm : Commutative _∨_
∨-comm true  true  = refl
∨-comm true  false = refl
∨-comm false true  = refl
∨-comm false false = refl

∨-identityˡ : LeftIdentity false _∨_
∨-identityˡ _ = refl

∨-identityʳ : RightIdentity false _∨_
∨-identityʳ false = refl
∨-identityʳ true  = refl

∨-identity : Identity false _∨_
∨-identity = ∨-identityˡ , ∨-identityʳ

∨-zeroˡ : LeftZero true _∨_
∨-zeroˡ _ = refl

∨-zeroʳ : RightZero true _∨_
∨-zeroʳ false = refl
∨-zeroʳ true  = refl

∨-zero : Zero true _∨_
∨-zero = ∨-zeroˡ , ∨-zeroʳ

∨-inverseˡ : LeftInverse true not _∨_
∨-inverseˡ false = refl
∨-inverseˡ true  = refl

∨-inverseʳ : RightInverse true not _∨_
∨-inverseʳ x = ∨-comm x (not x) ⟨ trans ⟩ ∨-inverseˡ x

∨-inverse : Inverse true not _∨_
∨-inverse = ∨-inverseˡ , ∨-inverseʳ

∨-idem : Idempotent _∨_
∨-idem false = refl
∨-idem true  = refl

∨-sel : Selective _∨_
∨-sel false y = inj₂ refl
∨-sel true y  = inj₁ refl

∨-isSemigroup : IsSemigroup _≡_ _∨_
∨-isSemigroup = record
  { isEquivalence = isEquivalence
  ; assoc         = ∨-assoc
  ; ∙-cong        = cong₂ _∨_
  }

∨-isCommutativeMonoid : IsCommutativeMonoid _≡_ _∨_ false
∨-isCommutativeMonoid = record
  { isSemigroup = ∨-isSemigroup
  ; identityˡ   = λ _ → refl
  ; comm        = ∨-comm
  }

------------------------------------------------------------------------
-- Properties of _∧_

∧-assoc : Associative _∧_
∧-assoc true  y z = refl
∧-assoc false y z = refl

∧-comm : Commutative _∧_
∧-comm true  true  = refl
∧-comm true  false = refl
∧-comm false true  = refl
∧-comm false false = refl

∧-identityˡ : LeftIdentity true _∧_
∧-identityˡ _ = refl

∧-identityʳ : RightIdentity true _∧_
∧-identityʳ false = refl
∧-identityʳ true  = refl

∧-identity : Identity true _∧_
∧-identity = ∧-identityˡ , ∧-identityʳ

∧-zeroˡ : LeftZero false _∧_
∧-zeroˡ _ = refl

∧-zeroʳ : RightZero false _∧_
∧-zeroʳ false = refl
∧-zeroʳ true  = refl

∧-zero : Zero false _∧_
∧-zero = ∧-zeroˡ , ∧-zeroʳ

∧-inverseˡ : LeftInverse false not _∧_
∧-inverseˡ false = refl
∧-inverseˡ true = refl

∧-inverseʳ : RightInverse false not _∧_
∧-inverseʳ x = ∧-comm x (not x) ⟨ trans ⟩ ∧-inverseˡ x

∧-inverse : Inverse false not _∧_
∧-inverse = ∧-inverseˡ , ∧-inverseʳ

∧-idem : Idempotent _∧_
∧-idem false = refl
∧-idem true  = refl

∧-sel : Selective _∧_
∧-sel false y = inj₁ refl
∧-sel true y  = inj₂ refl

∧-distribˡ-∨ : _∧_ DistributesOverˡ _∨_
∧-distribˡ-∨ true  y z = refl
∧-distribˡ-∨ false y z = refl

∧-distribʳ-∨ : _∧_ DistributesOverʳ _∨_
∧-distribʳ-∨ x y z = begin
  (y ∨ z) ∧ x     ≡⟨ ∧-comm (y ∨ z) x ⟩
  x ∧ (y ∨ z)     ≡⟨ ∧-distribˡ-∨ x y z ⟩
  x ∧ y ∨ x ∧ z  ≡⟨ cong₂ _∨_ (∧-comm x y) (∧-comm x z) ⟩
  y ∧ x ∨ z ∧ x  ∎

∧-distrib-∨ : _∧_ DistributesOver _∨_
∧-distrib-∨ = ∧-distribˡ-∨ , ∧-distribʳ-∨

∨-distribˡ-∧ : _∨_ DistributesOverˡ _∧_
∨-distribˡ-∧ true  y z = refl
∨-distribˡ-∧ false y z = refl

∨-distribʳ-∧ : _∨_ DistributesOverʳ _∧_
∨-distribʳ-∧ x y z = begin
  (y ∧ z) ∨ x         ≡⟨ ∨-comm (y ∧ z) x ⟩
  x ∨ (y ∧ z)         ≡⟨ ∨-distribˡ-∧ x y z ⟩
  (x ∨ y) ∧ (x ∨ z)  ≡⟨ cong₂ _∧_ (∨-comm x y) (∨-comm x z) ⟩
  (y ∨ x) ∧ (z ∨ x)  ∎

∨-distrib-∧ : _∨_ DistributesOver _∧_
∨-distrib-∧ = ∨-distribˡ-∧ , ∨-distribʳ-∧

∧-abs-∨ : _∧_ Absorbs _∨_
∧-abs-∨ true  y = refl
∧-abs-∨ false y = refl

∨-abs-∧ : _∨_ Absorbs _∧_
∨-abs-∧ true  y = refl
∨-abs-∧ false y = refl

∨-∧-absorptive : Absorptive _∨_ _∧_
∨-∧-absorptive = ∨-abs-∧ , ∧-abs-∨

∧-isSemigroup : IsSemigroup _≡_ _∧_
∧-isSemigroup = record
  { isEquivalence = isEquivalence
  ; assoc         = ∧-assoc
  ; ∙-cong        = cong₂ _∧_
  }

∧-isCommutativeMonoid : IsCommutativeMonoid _≡_ _∧_ true
∧-isCommutativeMonoid = record
  { isSemigroup = ∧-isSemigroup
  ; identityˡ   = λ _ → refl
  ; comm        = ∧-comm
  }

∨-∧-isCommutativeSemiring
  : IsCommutativeSemiring _≡_ _∨_ _∧_ false true
∨-∧-isCommutativeSemiring = record
  { +-isCommutativeMonoid = ∨-isCommutativeMonoid
  ; *-isCommutativeMonoid = ∧-isCommutativeMonoid
  ; distribʳ = ∧-distribʳ-∨
  ; zeroˡ    = λ _ → refl
  }

∨-∧-commutativeSemiring : CommutativeSemiring _ _
∨-∧-commutativeSemiring = record
  { _+_                   = _∨_
  ; _*_                   = _∧_
  ; 0#                    = false
  ; 1#                    = true
  ; isCommutativeSemiring = ∨-∧-isCommutativeSemiring
  }

∧-∨-isCommutativeSemiring
  : IsCommutativeSemiring _≡_ _∧_ _∨_ true false
∧-∨-isCommutativeSemiring = record
  { +-isCommutativeMonoid = ∧-isCommutativeMonoid
  ; *-isCommutativeMonoid = ∨-isCommutativeMonoid
  ; distribʳ = ∨-distribʳ-∧
  ; zeroˡ    = λ _ → refl
  }

∧-∨-commutativeSemiring : CommutativeSemiring _ _
∧-∨-commutativeSemiring = record
  { _+_                   = _∧_
  ; _*_                   = _∨_
  ; 0#                    = true
  ; 1#                    = false
  ; isCommutativeSemiring = ∧-∨-isCommutativeSemiring
  }

∨-∧-isLattice : IsLattice _≡_ _∨_ _∧_
∨-∧-isLattice = record
  { isEquivalence = isEquivalence
  ; ∨-comm        = ∨-comm
  ; ∨-assoc       = ∨-assoc
  ; ∨-cong        = cong₂ _∨_
  ; ∧-comm        = ∧-comm
  ; ∧-assoc       = ∧-assoc
  ; ∧-cong        = cong₂ _∧_
  ; absorptive    = ∨-∧-absorptive
  }

∨-∧-isDistributiveLattice : IsDistributiveLattice _≡_ _∨_ _∧_
∨-∧-isDistributiveLattice = record
  { isLattice     = ∨-∧-isLattice
  ; ∨-∧-distribʳ = ∨-distribʳ-∧
  }

∨-∧-isBooleanAlgebra : IsBooleanAlgebra _≡_ _∨_ _∧_ not true false
∨-∧-isBooleanAlgebra = record
  { isDistributiveLattice = ∨-∧-isDistributiveLattice
  ; ∨-complementʳ = ∨-inverseʳ
  ; ∧-complementʳ = ∧-inverseʳ
  ; ¬-cong        = cong not
  }

∨-∧-booleanAlgebra : BooleanAlgebra _ _
∨-∧-booleanAlgebra = record
  { _∨_              = _∨_
  ; _∧_              = _∧_
  ; ¬_               = not
  ; ⊤                = true
  ; ⊥                = false
  ; isBooleanAlgebra = ∨-∧-isBooleanAlgebra
  }

------------------------------------------------------------------------
-- Properties of _xor_

xor-is-ok : ∀ x y → x xor y ≡ (x ∨ y) ∧ not (x ∧ y)
xor-is-ok true  y = refl
xor-is-ok false y = sym (∧-identityʳ _)

xor-∧-commutativeRing : CommutativeRing _ _
xor-∧-commutativeRing = commutativeRing
  where
  import Algebra.Properties.BooleanAlgebra as BA
  open BA ∨-∧-booleanAlgebra
  open XorRing _xor_ xor-is-ok

------------------------------------------------------------------------
-- Miscellaneous other properties

not-involutive : Involutive not
not-involutive true  = refl
not-involutive false = refl

not-¬ : ∀ {x y} → x ≡ y → x ≢ not y
not-¬ {true}  refl ()
not-¬ {false} refl ()

¬-not : ∀ {x y} → x ≢ y → x ≡ not y
¬-not {true}  {true}  x≢y = ⊥-elim (x≢y refl)
¬-not {true}  {false} _   = refl
¬-not {false} {true}  _   = refl
¬-not {false} {false} x≢y = ⊥-elim (x≢y refl)

⇔→≡ : {b₁ b₂ b : Bool} → b₁ ≡ b ⇔ b₂ ≡ b → b₁ ≡ b₂
⇔→≡ {true } {true }         hyp = refl
⇔→≡ {true } {false} {true } hyp = sym (Equivalence.to hyp ⟨$⟩ refl)
⇔→≡ {true } {false} {false} hyp = Equivalence.from hyp ⟨$⟩ refl
⇔→≡ {false} {true } {true } hyp = Equivalence.from hyp ⟨$⟩ refl
⇔→≡ {false} {true } {false} hyp = sym (Equivalence.to hyp ⟨$⟩ refl)
⇔→≡ {false} {false}         hyp = refl

T-≡ : ∀ {b} → T b ⇔ b ≡ true
T-≡ {false} = equivalence (λ ())       (λ ())
T-≡ {true}  = equivalence (const refl) (const _)

T-not-≡ : ∀ {b} → T (not b) ⇔ b ≡ false
T-not-≡ {false} = equivalence (const refl) (const _)
T-not-≡ {true}  = equivalence (λ ())       (λ ())

T-∧ : ∀ {b₁ b₂} → T (b₁ ∧ b₂) ⇔ (T b₁ × T b₂)
T-∧ {true}  {true}  = equivalence (const (_ , _)) (const _)
T-∧ {true}  {false} = equivalence (λ ())          proj₂
T-∧ {false} {_}     = equivalence (λ ())          proj₁

T-∨ : ∀ {b₁ b₂} → T (b₁ ∨ b₂) ⇔ (T b₁ ⊎ T b₂)
T-∨ {true}  {b₂}    = equivalence inj₁ (const _)
T-∨ {false} {true}  = equivalence inj₂ (const _)
T-∨ {false} {false} = equivalence inj₁ [ id , id ]

proof-irrelevance : ∀ {b} (p q : T b) → p ≡ q
proof-irrelevance {true}  _  _  = refl
proof-irrelevance {false} () ()

push-function-into-if :
  ∀ {a b} {A : Set a} {B : Set b} (f : A → B) x {y z} →
  f (if x then y else z) ≡ (if x then f y else f z)
push-function-into-if _ true  = refl
push-function-into-if _ false = refl

------------------------------------------------------------------------
-- Modules for reasoning about boolean operations

module RingSolver =
  Solver (ACR.fromCommutativeSemiring ∨-∧-commutativeSemiring) _≟_

module XorRingSolver =
  Solver (ACR.fromCommutativeRing xor-∧-commutativeRing) _≟_

------------------------------------------------------------------------
-- DEPRECATED NAMES
------------------------------------------------------------------------
-- Please use the new names as continuing support for the old names is
-- not guaranteed.

∧-∨-distˡ   = ∧-distribˡ-∨
∧-∨-distʳ   = ∧-distribʳ-∨
distrib-∧-∨ = ∧-distrib-∨
∨-∧-distˡ   = ∨-distribˡ-∧
∨-∧-distʳ   = ∨-distribʳ-∧
∨-∧-distrib = ∨-distrib-∧
∨-∧-abs    = ∨-abs-∧
∧-∨-abs    = ∧-abs-∨

not-∧-inverseˡ = ∧-inverseˡ
not-∧-inverseʳ = ∧-inverseʳ
not-∧-inverse = ∧-inverse
not-∨-inverseˡ = ∨-inverseˡ
not-∨-inverseʳ = ∨-inverseʳ
not-∨-inverse = ∨-inverse

isCommutativeSemiring-∨-∧ = ∨-∧-isCommutativeSemiring
commutativeSemiring-∨-∧   =  ∨-∧-commutativeSemiring
isCommutativeSemiring-∧-∨ = ∧-∨-isCommutativeSemiring
commutativeSemiring-∧-∨   = ∧-∨-commutativeSemiring
isBooleanAlgebra           = ∨-∧-isBooleanAlgebra
booleanAlgebra             = ∨-∧-booleanAlgebra
commutativeRing-xor-∧     = xor-∧-commutativeRing

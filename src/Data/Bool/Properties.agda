------------------------------------------------------------------------
-- The Agda standard library
--
-- A bunch of properties
------------------------------------------------------------------------

module Data.Bool.Properties where

open import Data.Bool as Bool
open import Function
open import Function.Equality using (_⟨$⟩_)
open import Function.Equivalence
  using (_⇔_; equivalence; module Equivalence)
open import Algebra
open import Algebra.Structures
import Algebra.RingSolver.Simple as Solver
import Algebra.RingSolver.AlmostCommutativeRing as ACR
open import Relation.Binary.PropositionalEquality as P
  using (_≡_; _≢_; refl)
open P.≡-Reasoning
import Algebra.FunctionProperties as FP; open FP (_≡_ {A = Bool})
open import Data.Product
open import Data.Sum
open import Data.Empty

------------------------------------------------------------------------
-- Duality

-- Can we take advantage of duality in some (nice) way?

------------------------------------------------------------------------
-- (Bool, ∨, ∧, false, true) forms a commutative semiring

∨-assoc : Associative _∨_
∨-assoc true  y z = refl
∨-assoc false y z = refl

∧-assoc : Associative _∧_
∧-assoc true  y z = refl
∧-assoc false y z = refl

∨-comm : Commutative _∨_
∨-comm true  true  = refl
∨-comm true  false = refl
∨-comm false true  = refl
∨-comm false false = refl

∧-comm : Commutative _∧_
∧-comm true  true  = refl
∧-comm true  false = refl
∧-comm false true  = refl
∧-comm false false = refl

∧-∨-distˡ : _∧_ DistributesOverˡ _∨_
∧-∨-distˡ true  y z = refl
∧-∨-distˡ false y z = refl

∧-∨-distʳ : _∧_ DistributesOverʳ _∨_
∧-∨-distʳ x y z =
  begin
    (y ∨ z) ∧ x
  ≡⟨ ∧-comm (y ∨ z) x ⟩
    x ∧ (y ∨ z)
  ≡⟨ ∧-∨-distˡ x y z ⟩
    x ∧ y ∨ x ∧ z
  ≡⟨ P.cong₂ _∨_ (∧-comm x y) (∧-comm x z) ⟩
    y ∧ x ∨ z ∧ x
  ∎

distrib-∧-∨ : _∧_ DistributesOver _∨_
distrib-∧-∨ = ∧-∨-distˡ , ∧-∨-distʳ

isCommutativeSemiring-∨-∧
  : IsCommutativeSemiring _≡_ _∨_ _∧_ false true
isCommutativeSemiring-∨-∧ = record
  { +-isCommutativeMonoid = record
    { isSemigroup = record
      { isEquivalence = P.isEquivalence
      ; assoc         = ∨-assoc
      ; ∙-cong        = P.cong₂ _∨_
      }
    ; identityˡ = λ _ → refl
    ; comm      = ∨-comm
    }
  ; *-isCommutativeMonoid = record
    { isSemigroup = record
      { isEquivalence = P.isEquivalence
      ; assoc         = ∧-assoc
      ; ∙-cong        = P.cong₂ _∧_
      }
      ; identityˡ = λ _ → refl
    ; comm      = ∧-comm
    }
  ; distribʳ = proj₂ distrib-∧-∨
  ; zeroˡ    = λ _ → refl
  }

commutativeSemiring-∨-∧ : CommutativeSemiring _ _
commutativeSemiring-∨-∧ = record
  { _+_                   = _∨_
  ; _*_                   = _∧_
  ; 0#                    = false
  ; 1#                    = true
  ; isCommutativeSemiring = isCommutativeSemiring-∨-∧
  }

module RingSolver =
  Solver (ACR.fromCommutativeSemiring commutativeSemiring-∨-∧) _≟_

------------------------------------------------------------------------
-- (Bool, ∧, ∨, true, false) forms a commutative semiring

∨-∧-distˡ : _∨_ DistributesOverˡ _∧_
∨-∧-distˡ true  y z = refl
∨-∧-distˡ false y z = refl

∨-∧-distʳ : _∨_ DistributesOverʳ _∧_
∨-∧-distʳ x y z =
  begin
    (y ∧ z) ∨ x
  ≡⟨ ∨-comm (y ∧ z) x ⟩
    x ∨ (y ∧ z)
  ≡⟨ ∨-∧-distˡ x y z ⟩
    (x ∨ y) ∧ (x ∨ z)
  ≡⟨ P.cong₂ _∧_ (∨-comm x y) (∨-comm x z) ⟩
    (y ∨ x) ∧ (z ∨ x)
  ∎

∨-∧-distrib : _∨_ DistributesOver _∧_
∨-∧-distrib = ∨-∧-distˡ , ∨-∧-distʳ

isCommutativeSemiring-∧-∨
  : IsCommutativeSemiring _≡_ _∧_ _∨_ true false
isCommutativeSemiring-∧-∨ = record
  { +-isCommutativeMonoid = record
    { isSemigroup = record
      { isEquivalence = P.isEquivalence
      ; assoc         = ∧-assoc
      ; ∙-cong        = P.cong₂ _∧_
      }
    ; identityˡ = λ _ → refl
    ; comm      = ∧-comm
    }
  ; *-isCommutativeMonoid = record
    { isSemigroup = record
      { isEquivalence = P.isEquivalence
      ; assoc         = ∨-assoc
      ; ∙-cong        = P.cong₂ _∨_
      }
    ; identityˡ = λ _ → refl
    ; comm      = ∨-comm
    }
  ; distribʳ = ∨-∧-distʳ
  ; zeroˡ    = λ _ → refl
  }

commutativeSemiring-∧-∨ : CommutativeSemiring _ _
commutativeSemiring-∧-∨ = record
  { _+_                   = _∧_
  ; _*_                   = _∨_
  ; 0#                    = true
  ; 1#                    = false
  ; isCommutativeSemiring = isCommutativeSemiring-∧-∨
  }

------------------------------------------------------------------------
-- (Bool, ∨, ∧, not, true, false) is a boolean algebra

∨-∧-abs : _∨_ Absorbs _∧_
∨-∧-abs true  y = refl
∨-∧-abs false y = refl

∧-∨-abs : _∧_ Absorbs _∨_
∧-∨-abs true  y = refl
∧-∨-abs false y = refl

∨-∧-absorptive : Absorptive _∨_ _∧_
∨-∧-absorptive = ∨-∧-abs , ∧-∨-abs

not-∧-inverseˡ : LeftInverse false not _∧_
not-∧-inverseˡ false = refl
not-∧-inverseˡ true = refl

not-∧-inverseʳ : RightInverse false not _∧_
not-∧-inverseʳ x = ∧-comm x (not x) ⟨ P.trans ⟩ not-∧-inverseˡ x

not-∧-inverse : Inverse false not _∧_
not-∧-inverse = not-∧-inverseˡ , not-∧-inverseʳ

not-∨-inverseˡ : LeftInverse true not _∨_
not-∨-inverseˡ false = refl
not-∨-inverseˡ true  = refl

not-∨-inverseʳ : RightInverse true not _∨_
not-∨-inverseʳ x = ∨-comm x (not x) ⟨ P.trans ⟩ not-∨-inverseˡ x

not-∨-inverse : Inverse true not _∨_
not-∨-inverse = not-∨-inverseˡ , not-∨-inverseʳ

isBooleanAlgebra : IsBooleanAlgebra _≡_ _∨_ _∧_ not true false
isBooleanAlgebra = record
  { isDistributiveLattice = record
      { isLattice = record
          { isEquivalence = P.isEquivalence
          ; ∨-comm        = ∨-comm
          ; ∨-assoc       = ∨-assoc
          ; ∨-cong        = P.cong₂ _∨_
          ; ∧-comm        = ∧-comm
          ; ∧-assoc       = ∧-assoc
          ; ∧-cong        = P.cong₂ _∧_
          ; absorptive    = ∨-∧-absorptive
          }
      ; ∨-∧-distribʳ = ∨-∧-distʳ
      }
  ; ∨-complementʳ = not-∨-inverseʳ
  ; ∧-complementʳ = not-∧-inverseʳ
  ; ¬-cong        = P.cong not
  }

booleanAlgebra : BooleanAlgebra _ _
booleanAlgebra = record
  { _∨_              = _∨_
  ; _∧_              = _∧_
  ; ¬_               = not
  ; ⊤                = true
  ; ⊥                = false
  ; isBooleanAlgebra = isBooleanAlgebra
  }

------------------------------------------------------------------------
-- (Bool, xor, ∧, id, false, true) forms a commutative ring

xor-is-ok : ∀ x y → x xor y ≡ (x ∨ y) ∧ not (x ∧ y)
xor-is-ok true  y = refl
xor-is-ok false y = P.sym $ proj₂ CS.*-identity _
  where module CS = CommutativeSemiring commutativeSemiring-∨-∧

commutativeRing-xor-∧ : CommutativeRing _ _
commutativeRing-xor-∧ = commutativeRing
  where
  import Algebra.Properties.BooleanAlgebra as BA
  open BA booleanAlgebra
  open XorRing _xor_ xor-is-ok

module XorRingSolver =
  Solver (ACR.fromCommutativeRing commutativeRing-xor-∧) _≟_

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
⇔→≡ {true } {false} {true } hyp = P.sym (Equivalence.to hyp ⟨$⟩ refl)
⇔→≡ {true } {false} {false} hyp = Equivalence.from hyp ⟨$⟩ refl
⇔→≡ {false} {true } {true } hyp = Equivalence.from hyp ⟨$⟩ refl
⇔→≡ {false} {true } {false} hyp = P.sym (Equivalence.to hyp ⟨$⟩ refl)
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
push-function-into-if _ true  = P.refl
push-function-into-if _ false = P.refl

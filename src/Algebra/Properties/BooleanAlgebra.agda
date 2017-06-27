------------------------------------------------------------------------
-- The Agda standard library
--
-- Some derivable properties
------------------------------------------------------------------------

open import Algebra

module Algebra.Properties.BooleanAlgebra
         {b₁ b₂} (B : BooleanAlgebra b₁ b₂)
         where

open BooleanAlgebra B
import Algebra.Properties.DistributiveLattice
private
  open module DL = Algebra.Properties.DistributiveLattice
                     distributiveLattice public
    hiding (replace-equality)
open import Algebra.Structures
open import Algebra.FunctionProperties _≈_
open import Relation.Binary.EqReasoning setoid
open import Relation.Binary
open import Function
open import Function.Equality using (_⟨$⟩_)
open import Function.Equivalence using (_⇔_; module Equivalence)
open import Data.Product

------------------------------------------------------------------------
-- Some simple generalisations

∨-complementˡ : LeftInverse ⊤ ¬_ _∨_
∨-complementˡ x = begin
  ¬ x ∨ x    ≈⟨ ∨-comm _ _ ⟩
  x   ∨ ¬ x  ≈⟨ ∨-complementʳ _ ⟩
  ⊤          ∎

∨-complement : Inverse ⊤ ¬_ _∨_
∨-complement = ∨-complementˡ , ∨-complementʳ

∧-complementˡ : LeftInverse ⊥ ¬_ _∧_
∧-complementˡ x = begin
  ¬ x ∧ x    ≈⟨ ∧-comm _ _ ⟩
  x   ∧ ¬ x  ≈⟨ ∧-complementʳ _ ⟩
  ⊥          ∎

∧-complement : Inverse ⊥ ¬_ _∧_
∧-complement = ∧-complementˡ , ∧-complementʳ

------------------------------------------------------------------------
-- The dual construction is also a boolean algebra

∧-∨-isBooleanAlgebra : IsBooleanAlgebra _≈_ _∧_ _∨_ ¬_ ⊥ ⊤
∧-∨-isBooleanAlgebra = record
  { isDistributiveLattice = ∧-∨-isDistributiveLattice
  ; ∨-complementʳ         = ∧-complementʳ
  ; ∧-complementʳ         = ∨-complementʳ
  ; ¬-cong                = ¬-cong
  }

∧-∨-booleanAlgebra : BooleanAlgebra _ _
∧-∨-booleanAlgebra = record
  { _∧_              = _∨_
  ; _∨_              = _∧_
  ; ⊤                = ⊥
  ; ⊥                = ⊤
  ; isBooleanAlgebra = ∧-∨-isBooleanAlgebra
  }

------------------------------------------------------------------------
-- (∨, ∧, ⊥, ⊤) and (∧, ∨, ⊤, ⊥) are commutative semirings

∧-identityʳ : RightIdentity ⊤ _∧_
∧-identityʳ x = begin
  x ∧ ⊤          ≈⟨ refl ⟨ ∧-cong ⟩ sym (∨-complementʳ _) ⟩
  x ∧ (x ∨ ¬ x)  ≈⟨ proj₂ absorptive _ _ ⟩
  x              ∎

∧-identityˡ : LeftIdentity ⊤ _∧_
∧-identityˡ _ = ∧-comm _ _ ⟨ trans ⟩ ∧-identityʳ _

∧-identity : Identity ⊤ _∧_
∧-identity = ∧-identityˡ , ∧-identityʳ

∨-identityʳ : RightIdentity ⊥ _∨_
∨-identityʳ x = begin
  x ∨ ⊥          ≈⟨ refl ⟨ ∨-cong ⟩ sym (∧-complementʳ _) ⟩
  x ∨ x ∧ ¬ x    ≈⟨ proj₁ absorptive _ _ ⟩
  x              ∎

∨-identityˡ : LeftIdentity ⊥ _∨_
∨-identityˡ _ = ∨-comm _ _ ⟨ trans ⟩ ∨-identityʳ _

∨-identity : Identity ⊥ _∨_
∨-identity = ∨-identityˡ , ∨-identityʳ

∧-zeroʳ : RightZero ⊥ _∧_
∧-zeroʳ x = begin
  x ∧ ⊥          ≈⟨ refl ⟨ ∧-cong ⟩ sym (∧-complementʳ _) ⟩
  x ∧  x  ∧ ¬ x  ≈⟨ sym $ ∧-assoc _ _ _ ⟩
  (x ∧ x) ∧ ¬ x  ≈⟨ ∧-idempotent _ ⟨ ∧-cong ⟩ refl ⟩
  x       ∧ ¬ x  ≈⟨ ∧-complementʳ _ ⟩
  ⊥              ∎

∧-zeroˡ : LeftZero ⊥ _∧_
∧-zeroˡ _ = ∧-comm _ _ ⟨ trans ⟩ ∧-zeroʳ _

∧-zero : Zero ⊥ _∧_
∧-zero = ∧-zeroˡ , ∧-zeroʳ

∨-zeroʳ : ∀ x → x ∨ ⊤ ≈ ⊤
∨-zeroʳ x = begin
  x ∨ ⊤          ≈⟨ refl ⟨ ∨-cong ⟩ sym (∨-complementʳ _) ⟩
  x ∨  x  ∨ ¬ x  ≈⟨ sym $ ∨-assoc _ _ _ ⟩
  (x ∨ x) ∨ ¬ x  ≈⟨ ∨-idempotent _ ⟨ ∨-cong ⟩ refl ⟩
  x       ∨ ¬ x  ≈⟨ ∨-complementʳ _ ⟩
  ⊤              ∎

∨-zeroˡ : LeftZero ⊤ _∨_
∨-zeroˡ _ = ∨-comm _ _ ⟨ trans ⟩ ∨-zeroʳ _

∨-zero : Zero ⊤ _∨_
∨-zero = ∨-zeroˡ , ∨-zeroʳ

∨-isSemigroup : IsSemigroup _≈_ _∨_
∨-isSemigroup = record
  { isEquivalence = isEquivalence
  ; assoc         = ∨-assoc
  ; ∙-cong        = ∨-cong
  }

∧-isSemigroup : IsSemigroup _≈_ _∧_
∧-isSemigroup = record
  { isEquivalence = isEquivalence
  ; assoc         = ∧-assoc
  ; ∙-cong        = ∧-cong
  }

∨-⊥-isMonoid : IsMonoid _≈_ _∨_ ⊥
∨-⊥-isMonoid = record
  { isSemigroup = ∨-isSemigroup
  ; identity    = ∨-identity
  }

∧-⊤-isMonoid : IsMonoid _≈_ _∧_ ⊤
∧-⊤-isMonoid = record
  { isSemigroup = ∧-isSemigroup
  ; identity    = ∧-identity
  }

∨-⊥-isCommutativeMonoid : IsCommutativeMonoid _≈_ _∨_ ⊥
∨-⊥-isCommutativeMonoid = record
  { isSemigroup = ∨-isSemigroup
  ; identityˡ = ∨-identityˡ
  ; comm      = ∨-comm
  }

∧-⊤-isCommutativeMonoid : IsCommutativeMonoid _≈_ _∧_ ⊤
∧-⊤-isCommutativeMonoid = record
  { isSemigroup = ∧-isSemigroup
  ; identityˡ = ∧-identityˡ
  ; comm      = ∧-comm
  }

∨-∧-isCommutativeSemiring : IsCommutativeSemiring _≈_ _∨_ _∧_ ⊥ ⊤
∨-∧-isCommutativeSemiring = record
  { +-isCommutativeMonoid = ∨-⊥-isCommutativeMonoid
  ; *-isCommutativeMonoid = ∧-⊤-isCommutativeMonoid
  ; distribʳ = proj₂ ∧-∨-distrib
  ; zeroˡ    = ∧-zeroˡ
  }

∨-∧-commutativeSemiring : CommutativeSemiring _ _
∨-∧-commutativeSemiring = record
  { _+_                   = _∨_
  ; _*_                   = _∧_
  ; 0#                    = ⊥
  ; 1#                    = ⊤
  ; isCommutativeSemiring = ∨-∧-isCommutativeSemiring
  }

∧-∨-isCommutativeSemiring : IsCommutativeSemiring _≈_ _∧_ _∨_ ⊤ ⊥
∧-∨-isCommutativeSemiring = record
  { +-isCommutativeMonoid = ∧-⊤-isCommutativeMonoid
  ; *-isCommutativeMonoid = ∨-⊥-isCommutativeMonoid
  ; distribʳ = proj₂ ∨-∧-distrib
  ; zeroˡ    = ∨-zeroˡ
  }

∧-∨-commutativeSemiring : CommutativeSemiring _ _
∧-∨-commutativeSemiring = record
  { _+_                   = _∧_
  ; _*_                   = _∨_
  ; 0#                    = ⊤
  ; 1#                    = ⊥
  ; isCommutativeSemiring = ∧-∨-isCommutativeSemiring
  }

------------------------------------------------------------------------
-- Some other properties

-- I took the statement of this lemma (called Uniqueness of
-- Complements) from some course notes, "Boolean Algebra", written
-- by Gert Smolka.

private
  lemma : ∀ x y → x ∧ y ≈ ⊥ → x ∨ y ≈ ⊤ → ¬ x ≈ y
  lemma x y x∧y=⊥ x∨y=⊤ = begin
    ¬ x                ≈⟨ sym $ ∧-identityʳ _ ⟩
    ¬ x ∧ ⊤            ≈⟨ refl ⟨ ∧-cong ⟩ sym x∨y=⊤ ⟩
    ¬ x ∧ (x ∨ y)      ≈⟨ proj₁ ∧-∨-distrib _ _ _ ⟩
    ¬ x ∧ x ∨ ¬ x ∧ y  ≈⟨ ∧-complementˡ _ ⟨ ∨-cong ⟩ refl ⟩
    ⊥ ∨ ¬ x ∧ y        ≈⟨ sym x∧y=⊥ ⟨ ∨-cong ⟩ refl ⟩
    x ∧ y ∨ ¬ x ∧ y    ≈⟨ sym $ proj₂ ∧-∨-distrib _ _ _ ⟩
    (x ∨ ¬ x) ∧ y      ≈⟨ ∨-complementʳ _ ⟨ ∧-cong ⟩ refl ⟩
    ⊤ ∧ y              ≈⟨ ∧-identityˡ _ ⟩
    y                  ∎

¬⊥=⊤ : ¬ ⊥ ≈ ⊤
¬⊥=⊤ = lemma ⊥ ⊤ (∧-identityʳ _) (∨-zeroʳ _)

¬⊤=⊥ : ¬ ⊤ ≈ ⊥
¬⊤=⊥ = lemma ⊤ ⊥ (∧-zeroʳ _) (∨-identityʳ _)

¬-involutive : Involutive ¬_
¬-involutive x = lemma (¬ x) x (∧-complementˡ _) (∨-complementˡ _)

deMorgan₁ : ∀ x y → ¬ (x ∧ y) ≈ ¬ x ∨ ¬ y
deMorgan₁ x y = lemma (x ∧ y) (¬ x ∨ ¬ y) lem₁ lem₂
  where
  lem₁ = begin
    (x ∧ y) ∧ (¬ x ∨ ¬ y)          ≈⟨ proj₁ ∧-∨-distrib _ _ _ ⟩
    (x ∧ y) ∧ ¬ x ∨ (x ∧ y) ∧ ¬ y  ≈⟨ (∧-comm _ _ ⟨ ∧-cong ⟩ refl) ⟨ ∨-cong ⟩ refl ⟩
    (y ∧ x) ∧ ¬ x ∨ (x ∧ y) ∧ ¬ y  ≈⟨ ∧-assoc _ _ _ ⟨ ∨-cong ⟩ ∧-assoc _ _ _ ⟩
    y ∧ (x ∧ ¬ x) ∨ x ∧ (y ∧ ¬ y)  ≈⟨ (refl ⟨ ∧-cong ⟩ ∧-complementʳ _) ⟨ ∨-cong ⟩
                                      (refl ⟨ ∧-cong ⟩ ∧-complementʳ _) ⟩
    (y ∧ ⊥) ∨ (x ∧ ⊥)              ≈⟨ ∧-zeroʳ _ ⟨ ∨-cong ⟩ ∧-zeroʳ _ ⟩
    ⊥ ∨ ⊥                          ≈⟨ ∨-identityʳ _ ⟩
    ⊥                              ∎

  lem₃ = begin
    (x ∧ y) ∨ ¬ x          ≈⟨ proj₂ ∨-∧-distrib _ _ _ ⟩
    (x ∨ ¬ x) ∧ (y ∨ ¬ x)  ≈⟨ ∨-complementʳ _ ⟨ ∧-cong ⟩ refl ⟩
    ⊤ ∧ (y ∨ ¬ x)          ≈⟨ ∧-identityˡ _ ⟩
    y ∨ ¬ x                ≈⟨ ∨-comm _ _ ⟩
    ¬ x ∨ y                ∎

  lem₂ = begin
    (x ∧ y) ∨ (¬ x ∨ ¬ y)  ≈⟨ sym $ ∨-assoc _ _ _ ⟩
    ((x ∧ y) ∨ ¬ x) ∨ ¬ y  ≈⟨ lem₃ ⟨ ∨-cong ⟩ refl ⟩
    (¬ x ∨ y) ∨ ¬ y        ≈⟨ ∨-assoc _ _ _ ⟩
    ¬ x ∨ (y ∨ ¬ y)        ≈⟨ refl ⟨ ∨-cong ⟩ ∨-complementʳ _ ⟩
    ¬ x ∨ ⊤                ≈⟨ ∨-zeroʳ _ ⟩
    ⊤                      ∎

deMorgan₂ : ∀ x y → ¬ (x ∨ y) ≈ ¬ x ∧ ¬ y
deMorgan₂ x y = begin
  ¬ (x ∨ y)          ≈⟨ ¬-cong $ sym (¬-involutive _) ⟨ ∨-cong ⟩
                                 sym (¬-involutive _) ⟩
  ¬ (¬ ¬ x ∨ ¬ ¬ y)  ≈⟨ ¬-cong $ sym $ deMorgan₁ _ _ ⟩
  ¬ ¬ (¬ x ∧ ¬ y)    ≈⟨ ¬-involutive _ ⟩
  ¬ x ∧ ¬ y          ∎

-- One can replace the underlying equality with an equivalent one.

replace-equality :
  {_≈′_ : Rel Carrier b₂} →
  (∀ {x y} → x ≈ y ⇔ (x ≈′ y)) → BooleanAlgebra _ _
replace-equality {_≈′_} ≈⇔≈′ = record
  { _≈_              = _≈′_
  ; _∨_              = _∨_
  ; _∧_              = _∧_
  ; ¬_               = ¬_
  ; ⊤                = ⊤
  ; ⊥                = ⊥
  ; isBooleanAlgebra =  record
    { isDistributiveLattice = DistributiveLattice.isDistributiveLattice
                                (DL.replace-equality ≈⇔≈′)
    ; ∨-complementʳ         = λ x → to ⟨$⟩ ∨-complementʳ x
    ; ∧-complementʳ         = λ x → to ⟨$⟩ ∧-complementʳ x
    ; ¬-cong                = λ i≈j → to ⟨$⟩ ¬-cong (from ⟨$⟩ i≈j)
    }
  } where open module E {x y} = Equivalence (≈⇔≈′ {x} {y})

------------------------------------------------------------------------
-- (⊕, ∧, id, ⊥, ⊤) is a commutative ring

-- This construction is parameterised over the definition of xor.

module XorRing
  (xor : Op₂ Carrier)
  (⊕-def : ∀ x y → xor x y ≈ (x ∨ y) ∧ ¬ (x ∧ y))
  where

  private
    infixl 6 _⊕_

    _⊕_ : Op₂ Carrier
    _⊕_ = xor

    helper : ∀ {x y u v} → x ≈ y → u ≈ v → x ∧ ¬ u ≈ y ∧ ¬ v
    helper x≈y u≈v = x≈y ⟨ ∧-cong ⟩ ¬-cong u≈v

  ⊕-cong : Congruent₂ _⊕_
  ⊕-cong {x} {y} {u} {v} x≈y u≈v = begin
    x ⊕ u                ≈⟨ ⊕-def _ _ ⟩
    (x ∨ u) ∧ ¬ (x ∧ u)  ≈⟨ helper (x≈y ⟨ ∨-cong ⟩ u≈v)
                                   (x≈y ⟨ ∧-cong ⟩ u≈v) ⟩
    (y ∨ v) ∧ ¬ (y ∧ v)  ≈⟨ sym $ ⊕-def _ _ ⟩
    y ⊕ v                ∎

  ⊕-comm : Commutative _⊕_
  ⊕-comm x y = begin
    x ⊕ y                ≈⟨ ⊕-def _ _ ⟩
    (x ∨ y) ∧ ¬ (x ∧ y)  ≈⟨ helper (∨-comm _ _) (∧-comm _ _) ⟩
    (y ∨ x) ∧ ¬ (y ∧ x)  ≈⟨ sym $ ⊕-def _ _ ⟩
    y ⊕ x                ∎

  ⊕-¬-distribˡ : ∀ x y → ¬ (x ⊕ y) ≈ ¬ x ⊕ y
  ⊕-¬-distribˡ x y = begin
    ¬ (x ⊕ y)                              ≈⟨ ¬-cong $ ⊕-def _ _ ⟩
    ¬ ((x ∨ y) ∧ (¬ (x ∧ y)))              ≈⟨ ¬-cong (proj₂ ∧-∨-distrib _ _ _) ⟩
    ¬ ((x ∧ ¬ (x ∧ y)) ∨ (y ∧ ¬ (x ∧ y)))  ≈⟨ ¬-cong $
                                                refl ⟨ ∨-cong ⟩
                                                  (refl ⟨ ∧-cong ⟩
                                                     ¬-cong (∧-comm _ _)) ⟩
    ¬ ((x ∧ ¬ (x ∧ y)) ∨ (y ∧ ¬ (y ∧ x)))  ≈⟨ ¬-cong $ lem _ _ ⟨ ∨-cong ⟩ lem _ _ ⟩
    ¬ ((x ∧ ¬ y) ∨ (y ∧ ¬ x))              ≈⟨ deMorgan₂ _ _ ⟩
    ¬ (x ∧ ¬ y) ∧ ¬ (y ∧ ¬ x)              ≈⟨ deMorgan₁ _ _ ⟨ ∧-cong ⟩ refl ⟩
    (¬ x ∨ (¬ ¬ y)) ∧ ¬ (y ∧ ¬ x)          ≈⟨ helper (refl ⟨ ∨-cong ⟩ ¬-involutive _)
                                                     (∧-comm _ _) ⟩
    (¬ x ∨ y) ∧ ¬ (¬ x ∧ y)                ≈⟨ sym $ ⊕-def _ _ ⟩
    ¬ x ⊕ y                                ∎
    where
    lem : ∀ x y → x ∧ ¬ (x ∧ y) ≈ x ∧ ¬ y
    lem x y = begin
      x ∧ ¬ (x ∧ y)          ≈⟨ refl ⟨ ∧-cong ⟩ deMorgan₁ _ _ ⟩
      x ∧ (¬ x ∨ ¬ y)        ≈⟨ proj₁ ∧-∨-distrib _ _ _ ⟩
      (x ∧ ¬ x) ∨ (x ∧ ¬ y)  ≈⟨ ∧-complementʳ _ ⟨ ∨-cong ⟩ refl ⟩
      ⊥ ∨ (x ∧ ¬ y)          ≈⟨ ∨-identityˡ _ ⟩
      x ∧ ¬ y                ∎

  ⊕-¬-distribʳ : ∀ x y → ¬ (x ⊕ y) ≈ x ⊕ ¬ y
  ⊕-¬-distribʳ x y = begin
    ¬ (x ⊕ y)  ≈⟨ ¬-cong $ ⊕-comm _ _ ⟩
    ¬ (y ⊕ x)  ≈⟨ ⊕-¬-distribˡ _ _ ⟩
    ¬ y ⊕ x    ≈⟨ ⊕-comm _ _ ⟩
    x ⊕ ¬ y    ∎

  ⊕-annihilates-¬ : ∀ x y → x ⊕ y ≈ ¬ x ⊕ ¬ y
  ⊕-annihilates-¬ x y = begin
    x ⊕ y        ≈⟨ sym $ ¬-involutive _ ⟩
    ¬ ¬ (x ⊕ y)  ≈⟨ ¬-cong $ ⊕-¬-distribˡ _ _ ⟩
    ¬ (¬ x ⊕ y)  ≈⟨ ⊕-¬-distribʳ _ _ ⟩
    ¬ x ⊕ ¬ y    ∎

  ⊕-identityˡ : LeftIdentity ⊥ _⊕_
  ⊕-identityˡ x = begin
    ⊥ ⊕ x                ≈⟨ ⊕-def _ _ ⟩
    (⊥ ∨ x) ∧ ¬ (⊥ ∧ x)  ≈⟨ helper (∨-identityˡ _) (∧-zeroˡ _) ⟩
    x ∧ ¬ ⊥              ≈⟨ refl ⟨ ∧-cong ⟩ ¬⊥=⊤ ⟩
    x ∧ ⊤                ≈⟨ ∧-identityʳ _ ⟩
    x                    ∎

  ⊕-identityʳ : RightIdentity ⊥ _⊕_
  ⊕-identityʳ _ = ⊕-comm _ _ ⟨ trans ⟩ ⊕-identityˡ _

  ⊕-identity : Identity ⊥ _⊕_
  ⊕-identity = ⊕-identityˡ , ⊕-identityʳ

  ⊕-inverseˡ : LeftInverse ⊥ id _⊕_
  ⊕-inverseˡ x = begin
    x ⊕ x               ≈⟨ ⊕-def _ _ ⟩
    (x ∨ x) ∧ ¬ (x ∧ x) ≈⟨ helper (∨-idempotent _) (∧-idempotent _) ⟩
    x ∧ ¬ x             ≈⟨ ∧-complementʳ _ ⟩
    ⊥                   ∎

  ⊕-inverseʳ : RightInverse ⊥ id _⊕_
  ⊕-inverseʳ _ = ⊕-comm _ _ ⟨ trans ⟩ ⊕-inverseˡ _

  ⊕-inverse : Inverse ⊥ id _⊕_
  ⊕-inverse = ⊕-inverseˡ , ⊕-inverseʳ

  ∧-distribˡ-⊕ : _∧_ DistributesOverˡ _⊕_
  ∧-distribˡ-⊕ x y z = begin
    x ∧ (y ⊕ z)                ≈⟨ refl ⟨ ∧-cong ⟩ ⊕-def _ _ ⟩
    x ∧ ((y ∨ z) ∧ ¬ (y ∧ z))  ≈⟨ sym $ ∧-assoc _ _ _ ⟩
    (x ∧ (y ∨ z)) ∧ ¬ (y ∧ z)  ≈⟨ refl ⟨ ∧-cong ⟩ deMorgan₁ _ _ ⟩
    (x ∧ (y ∨ z)) ∧
    (¬ y ∨ ¬ z)                ≈⟨ sym $ ∨-identityˡ _ ⟩
    ⊥ ∨
    ((x ∧ (y ∨ z)) ∧
    (¬ y ∨ ¬ z))               ≈⟨ lem₃ ⟨ ∨-cong ⟩ refl ⟩
    ((x ∧ (y ∨ z)) ∧ ¬ x) ∨
    ((x ∧ (y ∨ z)) ∧
    (¬ y ∨ ¬ z))               ≈⟨ sym $ proj₁ ∧-∨-distrib _ _ _ ⟩
    (x ∧ (y ∨ z)) ∧
    (¬ x ∨ (¬ y ∨ ¬ z))        ≈⟨  refl ⟨ ∧-cong ⟩
                                  (refl ⟨ ∨-cong ⟩ sym (deMorgan₁ _ _)) ⟩
    (x ∧ (y ∨ z)) ∧
    (¬ x ∨ ¬ (y ∧ z))          ≈⟨ refl ⟨ ∧-cong ⟩ sym (deMorgan₁ _ _) ⟩
    (x ∧ (y ∨ z)) ∧
    ¬ (x ∧ (y ∧ z))            ≈⟨ helper refl lem₁ ⟩
    (x ∧ (y ∨ z)) ∧
    ¬ ((x ∧ y) ∧ (x ∧ z))      ≈⟨ proj₁ ∧-∨-distrib _ _ _ ⟨ ∧-cong ⟩
                                      refl ⟩
    ((x ∧ y) ∨ (x ∧ z)) ∧
    ¬ ((x ∧ y) ∧ (x ∧ z))      ≈⟨ sym $ ⊕-def _ _ ⟩
    (x ∧ y) ⊕ (x ∧ z)          ∎
      where
      lem₂ = begin
        x ∧ (y ∧ z)  ≈⟨ sym $ ∧-assoc _ _ _ ⟩
        (x ∧ y) ∧ z  ≈⟨ ∧-comm _ _ ⟨ ∧-cong ⟩ refl ⟩
        (y ∧ x) ∧ z  ≈⟨ ∧-assoc _ _ _ ⟩
        y ∧ (x ∧ z)  ∎

      lem₁ = begin
        x ∧ (y ∧ z)        ≈⟨ sym (∧-idempotent _) ⟨ ∧-cong ⟩ refl ⟩
        (x ∧ x) ∧ (y ∧ z)  ≈⟨ ∧-assoc _ _ _ ⟩
        x ∧ (x ∧ (y ∧ z))  ≈⟨ refl ⟨ ∧-cong ⟩ lem₂ ⟩
        x ∧ (y ∧ (x ∧ z))  ≈⟨ sym $ ∧-assoc _ _ _ ⟩
        (x ∧ y) ∧ (x ∧ z)  ∎

      lem₃ = begin
        ⊥                      ≈⟨ sym $ ∧-zeroʳ _ ⟩
        (y ∨ z) ∧ ⊥            ≈⟨ refl ⟨ ∧-cong ⟩ sym (∧-complementʳ _) ⟩
        (y ∨ z) ∧ (x ∧ ¬ x)    ≈⟨ sym $ ∧-assoc _ _ _ ⟩
        ((y ∨ z) ∧ x) ∧ ¬ x    ≈⟨ ∧-comm _ _ ⟨ ∧-cong ⟩ refl  ⟩
        (x ∧ (y ∨ z)) ∧ ¬ x    ∎

  ∧-distribʳ-⊕ : _∧_ DistributesOverʳ _⊕_
  ∧-distribʳ-⊕ x y z = begin
    (y ⊕ z) ∧ x        ≈⟨ ∧-comm _ _ ⟩
    x ∧ (y ⊕ z)        ≈⟨ ∧-distribˡ-⊕ _ _ _ ⟩
    (x ∧ y) ⊕ (x ∧ z)  ≈⟨ ∧-comm _ _ ⟨ ⊕-cong ⟩ ∧-comm _ _ ⟩
    (y ∧ x) ⊕ (z ∧ x)  ∎

  ∧-distrib-⊕ : _∧_ DistributesOver _⊕_
  ∧-distrib-⊕ = ∧-distribˡ-⊕ , ∧-distribʳ-⊕

  private

    lemma₂ : ∀ x y u v →
             (x ∧ y) ∨ (u ∧ v) ≈
             ((x ∨ u) ∧ (y ∨ u)) ∧
             ((x ∨ v) ∧ (y ∨ v))
    lemma₂ x y u v = begin
        (x ∧ y) ∨ (u ∧ v)              ≈⟨ proj₁ ∨-∧-distrib _ _ _ ⟩
        ((x ∧ y) ∨ u) ∧ ((x ∧ y) ∨ v)  ≈⟨ proj₂ ∨-∧-distrib _ _ _
                                            ⟨ ∧-cong ⟩
                                          proj₂ ∨-∧-distrib _ _ _ ⟩
        ((x ∨ u) ∧ (y ∨ u)) ∧
        ((x ∨ v) ∧ (y ∨ v))            ∎

  ⊕-assoc : Associative _⊕_
  ⊕-assoc x y z = sym $ begin
    x ⊕ (y ⊕ z)                                ≈⟨ refl ⟨ ⊕-cong ⟩ ⊕-def _ _ ⟩
    x ⊕ ((y ∨ z) ∧ ¬ (y ∧ z))                  ≈⟨ ⊕-def _ _ ⟩
      (x ∨ ((y ∨ z) ∧ ¬ (y ∧ z))) ∧
    ¬ (x ∧ ((y ∨ z) ∧ ¬ (y ∧ z)))              ≈⟨ lem₃ ⟨ ∧-cong ⟩ lem₄ ⟩
    (((x ∨ y) ∨ z) ∧ ((x ∨ ¬ y) ∨ ¬ z)) ∧
    (((¬ x ∨ ¬ y) ∨ z) ∧ ((¬ x ∨ y) ∨ ¬ z))    ≈⟨ ∧-assoc _ _ _ ⟩
    ((x ∨ y) ∨ z) ∧
    (((x ∨ ¬ y) ∨ ¬ z) ∧
     (((¬ x ∨ ¬ y) ∨ z) ∧ ((¬ x ∨ y) ∨ ¬ z)))  ≈⟨ refl ⟨ ∧-cong ⟩ lem₅ ⟩
    ((x ∨ y) ∨ z) ∧
    (((¬ x ∨ ¬ y) ∨ z) ∧
     (((x ∨ ¬ y) ∨ ¬ z) ∧ ((¬ x ∨ y) ∨ ¬ z)))  ≈⟨ sym $ ∧-assoc _ _ _ ⟩
    (((x ∨ y) ∨ z) ∧ ((¬ x ∨ ¬ y) ∨ z)) ∧
    (((x ∨ ¬ y) ∨ ¬ z) ∧ ((¬ x ∨ y) ∨ ¬ z))    ≈⟨ lem₁ ⟨ ∧-cong ⟩ lem₂ ⟩
      (((x ∨ y) ∧ ¬ (x ∧ y)) ∨ z) ∧
    ¬ (((x ∨ y) ∧ ¬ (x ∧ y)) ∧ z)              ≈⟨ sym $ ⊕-def _ _ ⟩
    ((x ∨ y) ∧ ¬ (x ∧ y)) ⊕ z                  ≈⟨ sym $ ⊕-def _ _ ⟨ ⊕-cong ⟩ refl ⟩
    (x ⊕ y) ⊕ z                                ∎
    where
    lem₁ = begin
      ((x ∨ y) ∨ z) ∧ ((¬ x ∨ ¬ y) ∨ z)  ≈⟨ sym $ proj₂ ∨-∧-distrib _ _ _ ⟩
      ((x ∨ y) ∧ (¬ x ∨ ¬ y)) ∨ z        ≈⟨ (refl ⟨ ∧-cong ⟩ sym (deMorgan₁ _ _))
                                                  ⟨ ∨-cong ⟩ refl ⟩
      ((x ∨ y) ∧ ¬ (x ∧ y)) ∨ z          ∎

    lem₂' = begin
      (x ∨ ¬ y) ∧ (¬ x ∨ y)              ≈⟨ sym $ ∧-identityˡ _ ⟨ ∧-cong ⟩ ∧-identityʳ _ ⟩
      (⊤ ∧ (x ∨ ¬ y)) ∧ ((¬ x ∨ y) ∧ ⊤)  ≈⟨ sym $
                                              (∨-complementˡ _ ⟨ ∧-cong ⟩ ∨-comm _ _)
                                                ⟨ ∧-cong ⟩
                                              (refl ⟨ ∧-cong ⟩ ∨-complementˡ _) ⟩
      ((¬ x ∨ x) ∧ (¬ y ∨ x)) ∧
      ((¬ x ∨ y) ∧ (¬ y ∨ y))            ≈⟨ sym $ lemma₂ _ _ _ _ ⟩
      (¬ x ∧ ¬ y) ∨ (x ∧ y)              ≈⟨ sym $ deMorgan₂ _ _ ⟨ ∨-cong ⟩ ¬-involutive _ ⟩
      ¬ (x ∨ y) ∨ ¬ ¬ (x ∧ y)            ≈⟨ sym (deMorgan₁ _ _) ⟩
      ¬ ((x ∨ y) ∧ ¬ (x ∧ y))            ∎

    lem₂ = begin
      ((x ∨ ¬ y) ∨ ¬ z) ∧ ((¬ x ∨ y) ∨ ¬ z)  ≈⟨ sym $ proj₂ ∨-∧-distrib _ _ _ ⟩
      ((x ∨ ¬ y) ∧ (¬ x ∨ y)) ∨ ¬ z          ≈⟨ lem₂' ⟨ ∨-cong ⟩ refl ⟩
      ¬ ((x ∨ y) ∧ ¬ (x ∧ y)) ∨ ¬ z          ≈⟨ sym $ deMorgan₁ _ _ ⟩
      ¬ (((x ∨ y) ∧ ¬ (x ∧ y)) ∧ z)          ∎

    lem₃ = begin
      x ∨ ((y ∨ z) ∧ ¬ (y ∧ z))          ≈⟨ refl ⟨ ∨-cong ⟩
                                              (refl ⟨ ∧-cong ⟩ deMorgan₁ _ _) ⟩
      x ∨ ((y ∨ z) ∧ (¬ y ∨ ¬ z))        ≈⟨ proj₁ ∨-∧-distrib _ _ _ ⟩
      (x ∨ (y ∨ z)) ∧ (x ∨ (¬ y ∨ ¬ z))  ≈⟨ sym (∨-assoc _ _ _) ⟨ ∧-cong ⟩
                                            sym (∨-assoc _ _ _) ⟩
      ((x ∨ y) ∨ z) ∧ ((x ∨ ¬ y) ∨ ¬ z)  ∎

    lem₄' = begin
      ¬ ((y ∨ z) ∧ ¬ (y ∧ z))    ≈⟨ deMorgan₁ _ _ ⟩
      ¬ (y ∨ z) ∨ ¬ ¬ (y ∧ z)    ≈⟨ deMorgan₂ _ _ ⟨ ∨-cong ⟩ ¬-involutive _ ⟩
      (¬ y ∧ ¬ z) ∨ (y ∧ z)      ≈⟨ lemma₂ _ _ _ _ ⟩
      ((¬ y ∨ y) ∧ (¬ z ∨ y)) ∧
      ((¬ y ∨ z) ∧ (¬ z ∨ z))    ≈⟨ (∨-complementˡ _ ⟨ ∧-cong ⟩ ∨-comm _ _)
                                      ⟨ ∧-cong ⟩
                                   (refl ⟨ ∧-cong ⟩ ∨-complementˡ _) ⟩
      (⊤ ∧ (y ∨ ¬ z)) ∧
      ((¬ y ∨ z) ∧ ⊤)            ≈⟨ ∧-identityˡ _ ⟨ ∧-cong ⟩ ∧-identityʳ _ ⟩
      (y ∨ ¬ z) ∧ (¬ y ∨ z)      ∎

    lem₄ = begin
      ¬ (x ∧ ((y ∨ z) ∧ ¬ (y ∧ z)))  ≈⟨ deMorgan₁ _ _ ⟩
      ¬ x ∨ ¬ ((y ∨ z) ∧ ¬ (y ∧ z))  ≈⟨ refl ⟨ ∨-cong ⟩ lem₄' ⟩
      ¬ x ∨ ((y ∨ ¬ z) ∧ (¬ y ∨ z))  ≈⟨ proj₁ ∨-∧-distrib _ _ _ ⟩
      (¬ x ∨ (y     ∨ ¬ z)) ∧
      (¬ x ∨ (¬ y ∨ z))              ≈⟨ sym (∨-assoc _ _ _) ⟨ ∧-cong ⟩
                                        sym (∨-assoc _ _ _) ⟩
      ((¬ x ∨ y)     ∨ ¬ z) ∧
      ((¬ x ∨ ¬ y) ∨ z)              ≈⟨ ∧-comm _ _ ⟩
      ((¬ x ∨ ¬ y) ∨ z) ∧
      ((¬ x ∨ y)     ∨ ¬ z)          ∎

    lem₅ = begin
      ((x ∨ ¬ y) ∨ ¬ z) ∧
      (((¬ x ∨ ¬ y) ∨ z) ∧ ((¬ x ∨ y) ∨ ¬ z))    ≈⟨ sym $ ∧-assoc _ _ _ ⟩
      (((x ∨ ¬ y) ∨ ¬ z) ∧ ((¬ x ∨ ¬ y) ∨ z)) ∧
      ((¬ x ∨ y) ∨ ¬ z)                          ≈⟨ ∧-comm _ _ ⟨ ∧-cong ⟩ refl ⟩
      (((¬ x ∨ ¬ y) ∨ z) ∧ ((x ∨ ¬ y) ∨ ¬ z)) ∧
      ((¬ x ∨ y) ∨ ¬ z)                          ≈⟨ ∧-assoc _ _ _ ⟩
      ((¬ x ∨ ¬ y) ∨ z) ∧
      (((x ∨ ¬ y) ∨ ¬ z) ∧ ((¬ x ∨ y) ∨ ¬ z))    ∎

  ⊕-isSemigroup : IsSemigroup _≈_ _⊕_
  ⊕-isSemigroup = record
    { isEquivalence = isEquivalence
    ; assoc         = ⊕-assoc
    ; ∙-cong        = ⊕-cong
    }

  ⊕-⊥-isMonoid : IsMonoid _≈_ _⊕_ ⊥
  ⊕-⊥-isMonoid = record
    { isSemigroup = ⊕-isSemigroup
    ; identity    = ⊕-identity
    }

  ⊕-⊥-isGroup : IsGroup _≈_ _⊕_ ⊥ id
  ⊕-⊥-isGroup = record
    { isMonoid = ⊕-⊥-isMonoid
    ; inverse  = ⊕-inverse
    ; ⁻¹-cong  = id
    }

  ⊕-⊥-isAbelianGroup : IsAbelianGroup _≈_ _⊕_ ⊥ id
  ⊕-⊥-isAbelianGroup = record
    { isGroup = ⊕-⊥-isGroup
    ; comm    = ⊕-comm
    }

  ⊕-∧-isRing : IsRing _≈_ _⊕_ _∧_ id ⊥ ⊤
  ⊕-∧-isRing = record
    { +-isAbelianGroup = ⊕-⊥-isAbelianGroup
    ; *-isMonoid = ∧-⊤-isMonoid
    ; distrib = ∧-distrib-⊕
    }

  isCommutativeRing : IsCommutativeRing _≈_ _⊕_ _∧_ id ⊥ ⊤
  isCommutativeRing = record
    { isRing = ⊕-∧-isRing
    ; *-comm = ∧-comm
    }

  commutativeRing : CommutativeRing _ _
  commutativeRing = record
    { _+_               = _⊕_
    ; _*_               = _∧_
    ; -_                = id
    ; 0#                = ⊥
    ; 1#                = ⊤
    ; isCommutativeRing = isCommutativeRing
    }

infixl 6 _⊕_

_⊕_ : Op₂ Carrier
x ⊕ y = (x ∨ y) ∧ ¬ (x ∧ y)

module DefaultXorRing = XorRing _⊕_ (λ _ _ → refl)

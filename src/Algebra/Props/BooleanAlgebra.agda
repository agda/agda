------------------------------------------------------------------------
-- The Agda standard library
--
-- Some derivable properties
------------------------------------------------------------------------

open import Algebra

module Algebra.Props.BooleanAlgebra
         {b₁ b₂} (B : BooleanAlgebra b₁ b₂)
         where

open BooleanAlgebra B
import Algebra.Props.DistributiveLattice
private
  open module DL = Algebra.Props.DistributiveLattice
                     distributiveLattice public
    hiding (replace-equality)
open import Algebra.Structures
import Algebra.FunctionProperties as P; open P _≈_
import Relation.Binary.EqReasoning as EqR; open EqR setoid
open import Relation.Binary
open import Function
open import Function.Equality using (_⟨$⟩_)
open import Function.Equivalence using (_⇔_; module Equivalence)
open import Data.Product

------------------------------------------------------------------------
-- Some simple generalisations

∨-complement : Inverse ⊤ ¬_ _∨_
∨-complement = ∨-complementˡ , ∨-complementʳ
  where
  ∨-complementˡ : LeftInverse ⊤ ¬_ _∨_
  ∨-complementˡ x = begin
    ¬ x ∨ x    ≈⟨ ∨-comm _ _ ⟩
    x   ∨ ¬ x  ≈⟨ ∨-complementʳ _ ⟩
    ⊤          ∎

∧-complement : Inverse ⊥ ¬_ _∧_
∧-complement = ∧-complementˡ , ∧-complementʳ
  where
  ∧-complementˡ : LeftInverse ⊥ ¬_ _∧_
  ∧-complementˡ x = begin
    ¬ x ∧ x    ≈⟨ ∧-comm _ _ ⟩
    x   ∧ ¬ x  ≈⟨ ∧-complementʳ _ ⟩
    ⊥          ∎

------------------------------------------------------------------------
-- The dual construction is also a boolean algebra

∧-∨-isBooleanAlgebra : IsBooleanAlgebra _≈_ _∧_ _∨_ ¬_ ⊥ ⊤
∧-∨-isBooleanAlgebra = record
  { isDistributiveLattice = ∧-∨-isDistributiveLattice
  ; ∨-complementʳ         = proj₂ ∧-complement
  ; ∧-complementʳ         = proj₂ ∨-complement
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
-- (∨, ∧, ⊥, ⊤) is a commutative semiring

private

  ∧-identity : Identity ⊤ _∧_
  ∧-identity = (λ _ → ∧-comm _ _ ⟨ trans ⟩ x∧⊤=x _) , x∧⊤=x
    where
    x∧⊤=x : ∀ x → x ∧ ⊤ ≈ x
    x∧⊤=x x = begin
      x ∧ ⊤          ≈⟨ refl ⟨ ∧-cong ⟩ sym (proj₂ ∨-complement _) ⟩
      x ∧ (x ∨ ¬ x)  ≈⟨ proj₂ absorptive _ _ ⟩
      x              ∎

  ∨-identity : Identity ⊥ _∨_
  ∨-identity = (λ _ → ∨-comm _ _ ⟨ trans ⟩ x∨⊥=x _) , x∨⊥=x
    where
    x∨⊥=x : ∀ x → x ∨ ⊥ ≈ x
    x∨⊥=x x = begin
      x ∨ ⊥          ≈⟨ refl ⟨ ∨-cong ⟩ sym (proj₂ ∧-complement _) ⟩
      x ∨ x ∧ ¬ x    ≈⟨ proj₁ absorptive _ _ ⟩
      x              ∎

  ∧-zero : Zero ⊥ _∧_
  ∧-zero = (λ _ → ∧-comm _ _ ⟨ trans ⟩ x∧⊥=⊥ _) , x∧⊥=⊥
    where
    x∧⊥=⊥ : ∀ x → x ∧ ⊥ ≈ ⊥
    x∧⊥=⊥ x = begin
      x ∧ ⊥          ≈⟨ refl ⟨ ∧-cong ⟩ sym (proj₂ ∧-complement _) ⟩
      x ∧  x  ∧ ¬ x  ≈⟨ sym $ ∧-assoc _ _ _ ⟩
      (x ∧ x) ∧ ¬ x  ≈⟨ ∧-idempotent _ ⟨ ∧-cong ⟩ refl ⟩
      x       ∧ ¬ x  ≈⟨ proj₂ ∧-complement _ ⟩
      ⊥              ∎

∨-∧-isCommutativeSemiring : IsCommutativeSemiring _≈_ _∨_ _∧_ ⊥ ⊤
∨-∧-isCommutativeSemiring = record
  { +-isCommutativeMonoid = record
    { isSemigroup = record
      { isEquivalence = isEquivalence
      ; assoc         = ∨-assoc
      ; ∙-cong        = ∨-cong
      }
    ; identityˡ = proj₁ ∨-identity
    ; comm      = ∨-comm
    }
  ; *-isCommutativeMonoid = record
    { isSemigroup = record
      { isEquivalence = isEquivalence
      ; assoc         = ∧-assoc
      ; ∙-cong        = ∧-cong
      }
    ; identityˡ = proj₁ ∧-identity
    ; comm      = ∧-comm
    }
  ; distribʳ = proj₂ ∧-∨-distrib
  ; zeroˡ    = proj₁ ∧-zero
  }

∨-∧-commutativeSemiring : CommutativeSemiring _ _
∨-∧-commutativeSemiring = record
  { _+_                   = _∨_
  ; _*_                   = _∧_
  ; 0#                    = ⊥
  ; 1#                    = ⊤
  ; isCommutativeSemiring = ∨-∧-isCommutativeSemiring
  }

------------------------------------------------------------------------
-- (∧, ∨, ⊤, ⊥) is a commutative semiring

private

  ∨-zero : Zero ⊤ _∨_
  ∨-zero = (λ _ → ∨-comm _ _ ⟨ trans ⟩ x∨⊤=⊤ _) , x∨⊤=⊤
    where
    x∨⊤=⊤ : ∀ x → x ∨ ⊤ ≈ ⊤
    x∨⊤=⊤ x = begin
      x ∨ ⊤          ≈⟨ refl ⟨ ∨-cong ⟩ sym (proj₂ ∨-complement _) ⟩
      x ∨  x  ∨ ¬ x  ≈⟨ sym $ ∨-assoc _ _ _ ⟩
      (x ∨ x) ∨ ¬ x  ≈⟨ ∨-idempotent _ ⟨ ∨-cong ⟩ refl ⟩
      x       ∨ ¬ x  ≈⟨ proj₂ ∨-complement _ ⟩
      ⊤              ∎

∧-∨-isCommutativeSemiring : IsCommutativeSemiring _≈_ _∧_ _∨_ ⊤ ⊥
∧-∨-isCommutativeSemiring = record
  { +-isCommutativeMonoid = record
    { isSemigroup = record
      { isEquivalence = isEquivalence
      ; assoc         = ∧-assoc
      ; ∙-cong        = ∧-cong
      }
    ; identityˡ = proj₁ ∧-identity
    ; comm      = ∧-comm
    }
  ; *-isCommutativeMonoid = record
    { isSemigroup = record
      { isEquivalence = isEquivalence
      ; assoc         = ∨-assoc
      ; ∙-cong        = ∨-cong
      }
    ; identityˡ = proj₁ ∨-identity
    ; comm      = ∨-comm
    }
  ; distribʳ = proj₂ ∨-∧-distrib
  ; zeroˡ    = proj₁ ∨-zero
  }

∧-∨-commutativeSemiring : CommutativeSemiring _ _
∧-∨-commutativeSemiring =
  record { isCommutativeSemiring = ∧-∨-isCommutativeSemiring }

------------------------------------------------------------------------
-- Some other properties

-- I took the statement of this lemma (called Uniqueness of
-- Complements) from some course notes, "Boolean Algebra", written
-- by Gert Smolka.

private
  lemma : ∀ x y → x ∧ y ≈ ⊥ → x ∨ y ≈ ⊤ → ¬ x ≈ y
  lemma x y x∧y=⊥ x∨y=⊤ = begin
    ¬ x                ≈⟨ sym $ proj₂ ∧-identity _ ⟩
    ¬ x ∧ ⊤            ≈⟨ refl ⟨ ∧-cong ⟩ sym x∨y=⊤ ⟩
    ¬ x ∧ (x ∨ y)      ≈⟨ proj₁ ∧-∨-distrib _ _ _ ⟩
    ¬ x ∧ x ∨ ¬ x ∧ y  ≈⟨ proj₁ ∧-complement _ ⟨ ∨-cong ⟩ refl ⟩
    ⊥ ∨ ¬ x ∧ y        ≈⟨ sym x∧y=⊥ ⟨ ∨-cong ⟩ refl ⟩
    x ∧ y ∨ ¬ x ∧ y    ≈⟨ sym $ proj₂ ∧-∨-distrib _ _ _ ⟩
    (x ∨ ¬ x) ∧ y      ≈⟨ proj₂ ∨-complement _ ⟨ ∧-cong ⟩ refl ⟩
    ⊤ ∧ y              ≈⟨ proj₁ ∧-identity _ ⟩
    y                  ∎

¬⊥=⊤ : ¬ ⊥ ≈ ⊤
¬⊥=⊤ = lemma ⊥ ⊤ (proj₂ ∧-identity _) (proj₂ ∨-zero _)

¬⊤=⊥ : ¬ ⊤ ≈ ⊥
¬⊤=⊥ = lemma ⊤ ⊥ (proj₂ ∧-zero _) (proj₂ ∨-identity _)

¬-involutive : Involutive ¬_
¬-involutive x = lemma (¬ x) x (proj₁ ∧-complement _) (proj₁ ∨-complement _)

deMorgan₁ : ∀ x y → ¬ (x ∧ y) ≈ ¬ x ∨ ¬ y
deMorgan₁ x y = lemma (x ∧ y) (¬ x ∨ ¬ y) lem₁ lem₂
  where
  lem₁ = begin
    (x ∧ y) ∧ (¬ x ∨ ¬ y)          ≈⟨ proj₁ ∧-∨-distrib _ _ _ ⟩
    (x ∧ y) ∧ ¬ x ∨ (x ∧ y) ∧ ¬ y  ≈⟨ (∧-comm _ _ ⟨ ∧-cong ⟩ refl) ⟨ ∨-cong ⟩ refl ⟩
    (y ∧ x) ∧ ¬ x ∨ (x ∧ y) ∧ ¬ y  ≈⟨ ∧-assoc _ _ _ ⟨ ∨-cong ⟩ ∧-assoc _ _ _ ⟩
    y ∧ (x ∧ ¬ x) ∨ x ∧ (y ∧ ¬ y)  ≈⟨ (refl ⟨ ∧-cong ⟩ proj₂ ∧-complement _) ⟨ ∨-cong ⟩
                                      (refl ⟨ ∧-cong ⟩ proj₂ ∧-complement _) ⟩
    (y ∧ ⊥) ∨ (x ∧ ⊥)              ≈⟨ proj₂ ∧-zero _ ⟨ ∨-cong ⟩ proj₂ ∧-zero _ ⟩
    ⊥ ∨ ⊥                          ≈⟨ proj₂ ∨-identity _ ⟩
    ⊥                              ∎

  lem₃ = begin
    (x ∧ y) ∨ ¬ x          ≈⟨ proj₂ ∨-∧-distrib _ _ _ ⟩
    (x ∨ ¬ x) ∧ (y ∨ ¬ x)  ≈⟨ proj₂ ∨-complement _ ⟨ ∧-cong ⟩ refl ⟩
    ⊤ ∧ (y ∨ ¬ x)          ≈⟨ proj₁ ∧-identity _ ⟩
    y ∨ ¬ x                ≈⟨ ∨-comm _ _ ⟩
    ¬ x ∨ y                ∎

  lem₂ = begin
    (x ∧ y) ∨ (¬ x ∨ ¬ y)  ≈⟨ sym $ ∨-assoc _ _ _ ⟩
    ((x ∧ y) ∨ ¬ x) ∨ ¬ y  ≈⟨ lem₃ ⟨ ∨-cong ⟩ refl ⟩
    (¬ x ∨ y) ∨ ¬ y        ≈⟨ ∨-assoc _ _ _ ⟩
    ¬ x ∨ (y ∨ ¬ y)        ≈⟨ refl ⟨ ∨-cong ⟩ proj₂ ∨-complement _ ⟩
    ¬ x ∨ ⊤                ≈⟨ proj₂ ∨-zero _ ⟩
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
  (∀ {x y} → x ≈ y ⇔ x ≈′ y) → BooleanAlgebra _ _
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

  private
    helper : ∀ {x y u v} → x ≈ y → u ≈ v → x ∧ ¬ u ≈ y ∧ ¬ v
    helper x≈y u≈v = x≈y ⟨ ∧-cong ⟩ ¬-cong u≈v

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
      (x ∧ ¬ x) ∨ (x ∧ ¬ y)  ≈⟨ proj₂ ∧-complement _ ⟨ ∨-cong ⟩ refl ⟩
      ⊥ ∨ (x ∧ ¬ y)          ≈⟨ proj₁ ∨-identity _ ⟩
      x ∧ ¬ y                ∎

  private
    ⊕-comm : Commutative _⊕_
    ⊕-comm x y = begin
      x ⊕ y                ≈⟨ ⊕-def _ _ ⟩
      (x ∨ y) ∧ ¬ (x ∧ y)  ≈⟨ helper (∨-comm _ _) (∧-comm _ _) ⟩
      (y ∨ x) ∧ ¬ (y ∧ x)  ≈⟨ sym $ ⊕-def _ _ ⟩
      y ⊕ x                ∎

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

  private
    ⊕-cong : _⊕_ Preserves₂ _≈_ ⟶ _≈_ ⟶ _≈_
    ⊕-cong {x} {y} {u} {v} x≈y u≈v = begin
      x ⊕ u                ≈⟨ ⊕-def _ _ ⟩
      (x ∨ u) ∧ ¬ (x ∧ u)  ≈⟨ helper (x≈y ⟨ ∨-cong ⟩ u≈v)
                                     (x≈y ⟨ ∧-cong ⟩ u≈v) ⟩
      (y ∨ v) ∧ ¬ (y ∧ v)  ≈⟨ sym $ ⊕-def _ _ ⟩
      y ⊕ v                ∎

    ⊕-identity : Identity ⊥ _⊕_
    ⊕-identity = ⊥⊕x=x , (λ _ → ⊕-comm _ _ ⟨ trans ⟩ ⊥⊕x=x _)
      where
      ⊥⊕x=x : ∀ x → ⊥ ⊕ x ≈ x
      ⊥⊕x=x x = begin
        ⊥ ⊕ x                ≈⟨ ⊕-def _ _ ⟩
        (⊥ ∨ x) ∧ ¬ (⊥ ∧ x)  ≈⟨ helper (proj₁ ∨-identity _)
                                       (proj₁ ∧-zero _) ⟩
        x ∧ ¬ ⊥              ≈⟨ refl ⟨ ∧-cong ⟩ ¬⊥=⊤ ⟩
        x ∧ ⊤                ≈⟨ proj₂ ∧-identity _ ⟩
        x                    ∎

    ⊕-inverse : Inverse ⊥ id _⊕_
    ⊕-inverse = x⊕x=⊥ , (λ _ → ⊕-comm _ _ ⟨ trans ⟩ x⊕x=⊥ _)
      where
      x⊕x=⊥ : ∀ x → x ⊕ x ≈ ⊥
      x⊕x=⊥ x = begin
        x ⊕ x                ≈⟨ ⊕-def _ _ ⟩
        (x ∨ x) ∧ ¬ (x ∧ x)  ≈⟨ helper (∨-idempotent _)
                                       (∧-idempotent _) ⟩
        x ∧ ¬ x              ≈⟨ proj₂ ∧-complement _ ⟩
        ⊥                    ∎

    distrib-∧-⊕ : _∧_ DistributesOver _⊕_
    distrib-∧-⊕ = distˡ , distʳ
      where
      distˡ : _∧_ DistributesOverˡ _⊕_
      distˡ x y z = begin
        x ∧ (y ⊕ z)                ≈⟨ refl ⟨ ∧-cong ⟩ ⊕-def _ _ ⟩
        x ∧ ((y ∨ z) ∧ ¬ (y ∧ z))  ≈⟨ sym $ ∧-assoc _ _ _ ⟩
        (x ∧ (y ∨ z)) ∧ ¬ (y ∧ z)  ≈⟨ refl ⟨ ∧-cong ⟩ deMorgan₁ _ _ ⟩
        (x ∧ (y ∨ z)) ∧
        (¬ y ∨ ¬ z)                ≈⟨ sym $ proj₁ ∨-identity _ ⟩
        ⊥ ∨
        ((x ∧ (y ∨ z)) ∧
         (¬ y ∨ ¬ z))              ≈⟨ lem₃ ⟨ ∨-cong ⟩ refl ⟩
        ((x ∧ (y ∨ z)) ∧ ¬ x) ∨
        ((x ∧ (y ∨ z)) ∧
         (¬ y ∨ ¬ z))              ≈⟨ sym $ proj₁ ∧-∨-distrib _ _ _ ⟩
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
          ⊥                      ≈⟨ sym $ proj₂ ∧-zero _ ⟩
          (y ∨ z) ∧ ⊥            ≈⟨ refl ⟨ ∧-cong ⟩ sym (proj₂ ∧-complement _) ⟩
          (y ∨ z) ∧ (x ∧ ¬ x)    ≈⟨ sym $ ∧-assoc _ _ _ ⟩
          ((y ∨ z) ∧ x) ∧ ¬ x    ≈⟨ ∧-comm _ _ ⟨ ∧-cong ⟩ refl  ⟩
          (x ∧ (y ∨ z)) ∧ ¬ x    ∎

      distʳ : _∧_ DistributesOverʳ _⊕_
      distʳ x y z = begin
        (y ⊕ z) ∧ x        ≈⟨ ∧-comm _ _ ⟩
        x ∧ (y ⊕ z)        ≈⟨ distˡ _ _ _ ⟩
        (x ∧ y) ⊕ (x ∧ z)  ≈⟨ ∧-comm _ _ ⟨ ⊕-cong ⟩ ∧-comm _ _ ⟩
        (y ∧ x) ⊕ (z ∧ x)  ∎

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
        (x ∨ ¬ y) ∧ (¬ x ∨ y)              ≈⟨ sym $
                                                proj₁ ∧-identity _
                                                  ⟨ ∧-cong ⟩
                                                proj₂ ∧-identity _ ⟩
        (⊤ ∧ (x ∨ ¬ y)) ∧ ((¬ x ∨ y) ∧ ⊤)  ≈⟨ sym $
                                                (proj₁ ∨-complement _ ⟨ ∧-cong ⟩ ∨-comm _ _)
                                                  ⟨ ∧-cong ⟩
                                                (refl ⟨ ∧-cong ⟩ proj₁ ∨-complement _) ⟩
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
        ((¬ y ∨ z) ∧ (¬ z ∨ z))    ≈⟨ (proj₁ ∨-complement _ ⟨ ∧-cong ⟩ ∨-comm _ _)
                                        ⟨ ∧-cong ⟩
                                      (refl ⟨ ∧-cong ⟩ proj₁ ∨-complement _) ⟩
        (⊤ ∧ (y ∨ ¬ z)) ∧
        ((¬ y ∨ z) ∧ ⊤)            ≈⟨ proj₁ ∧-identity _ ⟨ ∧-cong ⟩
                                      proj₂ ∧-identity _ ⟩
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

  isCommutativeRing : IsCommutativeRing _≈_ _⊕_ _∧_ id ⊥ ⊤
  isCommutativeRing = record
    { isRing = record
      { +-isAbelianGroup = record
        { isGroup = record
          { isMonoid = record
            { isSemigroup = record
              { isEquivalence = isEquivalence
              ; assoc         = ⊕-assoc
              ; ∙-cong        = ⊕-cong
              }
            ; identity = ⊕-identity
            }
          ; inverse   = ⊕-inverse
          ; ⁻¹-cong   = id
          }
        ; comm = ⊕-comm
        }
      ; *-isMonoid = record
        { isSemigroup = record
          { isEquivalence = isEquivalence
          ; assoc         = ∧-assoc
          ; ∙-cong        = ∧-cong
          }
        ; identity = ∧-identity
        }
      ; distrib = distrib-∧-⊕
      }
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

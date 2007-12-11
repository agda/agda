------------------------------------------------------------------------
-- Some derivable properties
------------------------------------------------------------------------

open import Algebra

module Algebra.Props.BooleanAlgebra (b : BooleanAlgebra) where

open BooleanAlgebra b
import Algebra.Props.DistributiveLattice as DL
open DL distributiveLattice public
import Algebra.Structures as S; open S setoid
import Algebra.FunctionProperties as P; open P setoid
import Relation.Binary.EqReasoning as EqR; open EqR setoid
open import Relation.Binary
open import Data.Function
open import Data.Product

------------------------------------------------------------------------
-- Some simple generalisations

abstract
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

abstract

  ∧-∨-isBooleanAlgebra : IsBooleanAlgebra _∧_ _∨_ ¬_ ⊥ ⊤
  ∧-∨-isBooleanAlgebra = record
    { isDistributiveLattice = ∧-∨-isDistributiveLattice
    ; ∨-complementʳ         = proj₂ ∧-complement
    ; ∧-complementʳ         = proj₂ ∨-complement
    ; ¬-pres-≈              = ¬-pres-≈
    }

∧-∨-booleanAlgebra : BooleanAlgebra
∧-∨-booleanAlgebra = record
  { setoid           = setoid
  ; _∧_              = _∨_
  ; _∨_              = _∧_
  ; ¬_               = ¬_
  ; ⊤                = ⊥
  ; ⊥                = ⊤
  ; isBooleanAlgebra = ∧-∨-isBooleanAlgebra
  }


------------------------------------------------------------------------
-- (∨, ∧, ⊥, ⊤) is a commutative semiring

abstract
 private

  ∧-identity : Identity ⊤ _∧_
  ∧-identity = (\_ -> ∧-comm _ _ ⟨ trans ⟩ x∧⊤=x _) , x∧⊤=x
    where
    x∧⊤=x : forall x -> x ∧ ⊤ ≈ x
    x∧⊤=x x = begin
      x ∧ ⊤          ≈⟨ byDef ⟨ ∧-pres-≈ ⟩ sym (proj₂ ∨-complement _) ⟩
      x ∧ (x ∨ ¬ x)  ≈⟨ proj₂ absorptive _ _ ⟩
      x              ∎

  ∨-identity : Identity ⊥ _∨_
  ∨-identity = (\_ -> ∨-comm _ _ ⟨ trans ⟩ x∨⊥=x _) , x∨⊥=x
    where
    x∨⊥=x : forall x -> x ∨ ⊥ ≈ x
    x∨⊥=x x = begin
      x ∨ ⊥          ≈⟨ byDef ⟨ ∨-pres-≈ ⟩ sym (proj₂ ∧-complement _) ⟩
      x ∨ x ∧ ¬ x    ≈⟨ proj₁ absorptive _ _ ⟩
      x              ∎

  ∧-zero : Zero ⊥ _∧_
  ∧-zero = (\_ -> ∧-comm _ _ ⟨ trans ⟩ x∧⊥=⊥ _) , x∧⊥=⊥
    where
    x∧⊥=⊥ : forall x -> x ∧ ⊥ ≈ ⊥
    x∧⊥=⊥ x = begin
      x ∧ ⊥          ≈⟨ byDef ⟨ ∧-pres-≈ ⟩ sym (proj₂ ∧-complement _) ⟩
      x ∧  x  ∧ ¬ x  ≈⟨ sym $ ∧-assoc _ _ _ ⟩
      (x ∧ x) ∧ ¬ x  ≈⟨ ∧-idempotent _ ⟨ ∧-pres-≈ ⟩ byDef ⟩
      x       ∧ ¬ x  ≈⟨ proj₂ ∧-complement _ ⟩
      ⊥              ∎

abstract

  ∨-∧-isCommutativeSemiring : IsCommutativeSemiring _∨_ _∧_ ⊥ ⊤
  ∨-∧-isCommutativeSemiring = record
    { isSemiring = record
      { isSemiringWithoutAnnihilatingZero = record
        { +-isCommutativeMonoid = record
          { isMonoid = record
            { isSemigroup = record
              { assoc    = ∨-assoc
              ; •-pres-≈ = ∨-pres-≈
              }
            ; identity  = ∨-identity
            }
          ; comm  = ∨-comm
          }
        ; *-isMonoid = record
          { isSemigroup = record
            { assoc    = ∧-assoc
            ; •-pres-≈ = ∧-pres-≈
            }
          ; identity = ∧-identity
          }
        ; distrib = ∧-∨-distrib
        }
      ; zero = ∧-zero
      }
    ; *-comm = ∧-comm
    }

∨-∧-commutativeSemiring : CommutativeSemiring
∨-∧-commutativeSemiring = record
  { setoid                = setoid
  ; _+_                   = _∨_
  ; _*_                   = _∧_
  ; 0#                    = ⊥
  ; 1#                    = ⊤
  ; isCommutativeSemiring = ∨-∧-isCommutativeSemiring
  }

------------------------------------------------------------------------
-- (∧, ∨, ⊤, ⊥) is a commutative semiring

abstract
 private

  ∨-zero : Zero ⊤ _∨_
  ∨-zero = (\_ -> ∨-comm _ _ ⟨ trans ⟩ x∨⊤=⊤ _) , x∨⊤=⊤
    where
    x∨⊤=⊤ : forall x -> x ∨ ⊤ ≈ ⊤
    x∨⊤=⊤ x = begin
      x ∨ ⊤          ≈⟨ byDef ⟨ ∨-pres-≈ ⟩ sym (proj₂ ∨-complement _) ⟩
      x ∨  x  ∨ ¬ x  ≈⟨ sym $ ∨-assoc _ _ _ ⟩
      (x ∨ x) ∨ ¬ x  ≈⟨ ∨-idempotent _ ⟨ ∨-pres-≈ ⟩ byDef ⟩
      x       ∨ ¬ x  ≈⟨ proj₂ ∨-complement _ ⟩
      ⊤              ∎

abstract

  ∧-∨-isCommutativeSemiring : IsCommutativeSemiring _∧_ _∨_ ⊤ ⊥
  ∧-∨-isCommutativeSemiring = record
    { isSemiring = record
      { isSemiringWithoutAnnihilatingZero = record
        { +-isCommutativeMonoid = record
          { isMonoid = record
            { isSemigroup = record
              { assoc    = ∧-assoc
              ; •-pres-≈ = ∧-pres-≈
              }
            ; identity  = ∧-identity
            }
          ; comm  = ∧-comm
          }
        ; *-isMonoid = record
          { isSemigroup = record
            { assoc    = ∨-assoc
            ; •-pres-≈ = ∨-pres-≈
            }
          ; identity = ∨-identity
          }
        ; distrib = ∨-∧-distrib
        }
      ; zero = ∨-zero
      }
    ; *-comm = ∨-comm
    }

∧-∨-commutativeSemiring : CommutativeSemiring
∧-∨-commutativeSemiring = record
  { setoid                = setoid
  ; _+_                   = _∧_
  ; _*_                   = _∨_
  ; 0#                    = ⊤
  ; 1#                    = ⊥
  ; isCommutativeSemiring = ∧-∨-isCommutativeSemiring
  }

------------------------------------------------------------------------
-- Some other properties

abstract

  -- I took the statement of this lemma (called Uniqueness of
  -- Complements) from some course notes, "Boolean Algebra", written
  -- by Gert Smolka.

  private
    lemma : forall x y -> x ∧ y ≈ ⊥ -> x ∨ y ≈ ⊤ -> ¬ x ≈ y
    lemma x y x∧y=⊥ x∨y=⊤ = begin
      ¬ x                ≈⟨ sym $ proj₂ ∧-identity _ ⟩
      ¬ x ∧ ⊤            ≈⟨ byDef ⟨ ∧-pres-≈ ⟩ sym x∨y=⊤ ⟩
      ¬ x ∧ (x ∨ y)      ≈⟨ proj₁ ∧-∨-distrib _ _ _ ⟩
      ¬ x ∧ x ∨ ¬ x ∧ y  ≈⟨ proj₁ ∧-complement _ ⟨ ∨-pres-≈ ⟩ byDef ⟩
      ⊥ ∨ ¬ x ∧ y        ≈⟨ sym x∧y=⊥ ⟨ ∨-pres-≈ ⟩ byDef ⟩
      x ∧ y ∨ ¬ x ∧ y    ≈⟨ sym $ proj₂ ∧-∨-distrib _ _ _ ⟩
      (x ∨ ¬ x) ∧ y      ≈⟨ proj₂ ∨-complement _ ⟨ ∧-pres-≈ ⟩ byDef ⟩
      ⊤ ∧ y              ≈⟨ proj₁ ∧-identity _ ⟩
      y                  ∎

  ¬⊥=⊤ : ¬ ⊥ ≈ ⊤
  ¬⊥=⊤ = lemma ⊥ ⊤ (proj₂ ∧-identity _) (proj₂ ∨-zero _)

  ¬⊤=⊥ : ¬ ⊤ ≈ ⊥
  ¬⊤=⊥ = lemma ⊤ ⊥ (proj₂ ∧-zero _) (proj₂ ∨-identity _)

  ¬-involutive : Involutive ¬_
  ¬-involutive x = lemma (¬ x) x (proj₁ ∧-complement _) (proj₁ ∨-complement _)

  deMorgan₁ : forall x y -> ¬ (x ∧ y) ≈ ¬ x ∨ ¬ y
  deMorgan₁ x y = lemma (x ∧ y) (¬ x ∨ ¬ y) lem₁ lem₂
    where
    lem₁ = begin
      (x ∧ y) ∧ (¬ x ∨ ¬ y)          ≈⟨ proj₁ ∧-∨-distrib _ _ _ ⟩
      (x ∧ y) ∧ ¬ x ∨ (x ∧ y) ∧ ¬ y  ≈⟨ (∧-comm _ _ ⟨ ∧-pres-≈ ⟩ byDef) ⟨ ∨-pres-≈ ⟩ byDef ⟩
      (y ∧ x) ∧ ¬ x ∨ (x ∧ y) ∧ ¬ y  ≈⟨ ∧-assoc _ _ _ ⟨ ∨-pres-≈ ⟩ ∧-assoc _ _ _ ⟩
      y ∧ (x ∧ ¬ x) ∨ x ∧ (y ∧ ¬ y)  ≈⟨ (byDef ⟨ ∧-pres-≈ ⟩ proj₂ ∧-complement _) ⟨ ∨-pres-≈ ⟩
                                        (byDef ⟨ ∧-pres-≈ ⟩ proj₂ ∧-complement _) ⟩
      (y ∧ ⊥) ∨ (x ∧ ⊥)              ≈⟨ proj₂ ∧-zero _ ⟨ ∨-pres-≈ ⟩ proj₂ ∧-zero _ ⟩
      ⊥ ∨ ⊥                          ≈⟨ proj₂ ∨-identity _ ⟩
      ⊥                              ∎

    lem₃ = begin
      (x ∧ y) ∨ ¬ x          ≈⟨ proj₂ ∨-∧-distrib _ _ _ ⟩
      (x ∨ ¬ x) ∧ (y ∨ ¬ x)  ≈⟨ proj₂ ∨-complement _ ⟨ ∧-pres-≈ ⟩ byDef ⟩
      ⊤ ∧ (y ∨ ¬ x)          ≈⟨ proj₁ ∧-identity _ ⟩
      y ∨ ¬ x                ≈⟨ ∨-comm _ _ ⟩
      ¬ x ∨ y                ∎

    lem₂ = begin
      (x ∧ y) ∨ (¬ x ∨ ¬ y)  ≈⟨ sym $ ∨-assoc _ _ _ ⟩
      ((x ∧ y) ∨ ¬ x) ∨ ¬ y  ≈⟨ lem₃ ⟨ ∨-pres-≈ ⟩ byDef ⟩
      (¬ x ∨ y) ∨ ¬ y        ≈⟨ ∨-assoc _ _ _ ⟩
      ¬ x ∨ (y ∨ ¬ y)        ≈⟨ byDef ⟨ ∨-pres-≈ ⟩ proj₂ ∨-complement _ ⟩
      ¬ x ∨ ⊤                ≈⟨ proj₂ ∨-zero _ ⟩
      ⊤                      ∎

  deMorgan₂ : forall x y -> ¬ (x ∨ y) ≈ ¬ x ∧ ¬ y
  deMorgan₂ x y = begin
    ¬ (x ∨ y)          ≈⟨ ¬-pres-≈ $ sym (¬-involutive _) ⟨ ∨-pres-≈ ⟩
                                     sym (¬-involutive _) ⟩
    ¬ (¬ ¬ x ∨ ¬ ¬ y)  ≈⟨ ¬-pres-≈ $ sym $ deMorgan₁ _ _ ⟩
    ¬ ¬ (¬ x ∧ ¬ y)    ≈⟨ ¬-involutive _ ⟩
    ¬ x ∧ ¬ y          ∎

------------------------------------------------------------------------
-- (⊕, ∧, id, ⊥, ⊤) is a commutative ring

-- This construction is parameterised over the definition of xor.

module XorRing
  (xor : Op₂)
  (⊕-def : forall x y -> xor x y ≈ (x ∨ y) ∧ ¬ (x ∧ y))
  where

  private
    infixl 6 _⊕_

    _⊕_ : Op₂
    _⊕_ = xor

  abstract
    private
      helper :  forall {x y u v}
             -> x ≈ y -> u ≈ v -> x ∧ ¬ u ≈ y ∧ ¬ v
      helper x≈y u≈v = x≈y ⟨ ∧-pres-≈ ⟩ ¬-pres-≈ u≈v

    ⊕-¬-distribˡ : forall x y -> ¬ (x ⊕ y) ≈ ¬ x ⊕ y
    ⊕-¬-distribˡ x y = begin
      ¬ (x ⊕ y)                              ≈⟨ ¬-pres-≈ $ ⊕-def _ _ ⟩
      ¬ ((x ∨ y) ∧ (¬ (x ∧ y)))              ≈⟨ ¬-pres-≈ (proj₂ ∧-∨-distrib _ _ _) ⟩
      ¬ ((x ∧ ¬ (x ∧ y)) ∨ (y ∧ ¬ (x ∧ y)))  ≈⟨ ¬-pres-≈ $
                                                  byDef ⟨ ∨-pres-≈ ⟩
                                                    (byDef ⟨ ∧-pres-≈ ⟩
                                                       ¬-pres-≈ (∧-comm _ _)) ⟩
      ¬ ((x ∧ ¬ (x ∧ y)) ∨ (y ∧ ¬ (y ∧ x)))  ≈⟨ ¬-pres-≈ $ lem _ _ ⟨ ∨-pres-≈ ⟩ lem _ _ ⟩
      ¬ ((x ∧ ¬ y) ∨ (y ∧ ¬ x))              ≈⟨ deMorgan₂ _ _ ⟩
      ¬ (x ∧ ¬ y) ∧ ¬ (y ∧ ¬ x)              ≈⟨ deMorgan₁ _ _ ⟨ ∧-pres-≈ ⟩ byDef ⟩
      (¬ x ∨ (¬ ¬ y)) ∧ ¬ (y ∧ ¬ x)          ≈⟨ helper (byDef ⟨ ∨-pres-≈ ⟩ ¬-involutive _)
                                                       (∧-comm _ _) ⟩
      (¬ x ∨ y) ∧ ¬ (¬ x ∧ y)                ≈⟨ sym $ ⊕-def _ _ ⟩
      ¬ x ⊕ y                                ∎
      where
      lem : forall x y -> x ∧ ¬ (x ∧ y) ≈ x ∧ ¬ y
      lem x y = begin
        x ∧ ¬ (x ∧ y)          ≈⟨ byDef ⟨ ∧-pres-≈ ⟩ deMorgan₁ _ _ ⟩
        x ∧ (¬ x ∨ ¬ y)        ≈⟨ proj₁ ∧-∨-distrib _ _ _ ⟩
        (x ∧ ¬ x) ∨ (x ∧ ¬ y)  ≈⟨ proj₂ ∧-complement _ ⟨ ∨-pres-≈ ⟩ byDef ⟩
        ⊥ ∨ (x ∧ ¬ y)          ≈⟨ proj₁ ∨-identity _ ⟩
        x ∧ ¬ y                ∎

    private
      ⊕-comm : Commutative _⊕_
      ⊕-comm x y = begin
        x ⊕ y                ≈⟨ ⊕-def _ _ ⟩
        (x ∨ y) ∧ ¬ (x ∧ y)  ≈⟨ helper (∨-comm _ _) (∧-comm _ _) ⟩
        (y ∨ x) ∧ ¬ (y ∧ x)  ≈⟨ sym $ ⊕-def _ _ ⟩
        y ⊕ x                ∎

    ⊕-¬-distribʳ : forall x y -> ¬ (x ⊕ y) ≈ x ⊕ ¬ y
    ⊕-¬-distribʳ x y = begin
      ¬ (x ⊕ y)  ≈⟨ ¬-pres-≈ $ ⊕-comm _ _ ⟩
      ¬ (y ⊕ x)  ≈⟨ ⊕-¬-distribˡ _ _ ⟩
      ¬ y ⊕ x    ≈⟨ ⊕-comm _ _ ⟩
      x ⊕ ¬ y    ∎

    ⊕-annihilates-¬ : forall x y -> x ⊕ y ≈ ¬ x ⊕ ¬ y
    ⊕-annihilates-¬ x y = begin
      x ⊕ y        ≈⟨ sym $ ¬-involutive _ ⟩
      ¬ ¬ (x ⊕ y)  ≈⟨ ¬-pres-≈ $ ⊕-¬-distribˡ _ _ ⟩
      ¬ (¬ x ⊕ y)  ≈⟨ ⊕-¬-distribʳ _ _ ⟩
      ¬ x ⊕ ¬ y    ∎

    private
      ⊕-pres : _⊕_ Preserves₂ _≈_ → _≈_ → _≈_
      ⊕-pres {x} {y} {u} {v} x≈y u≈v = begin
        x ⊕ u                ≈⟨ ⊕-def _ _ ⟩
        (x ∨ u) ∧ ¬ (x ∧ u)  ≈⟨ helper (x≈y ⟨ ∨-pres-≈ ⟩ u≈v)
                                       (x≈y ⟨ ∧-pres-≈ ⟩ u≈v) ⟩
        (y ∨ v) ∧ ¬ (y ∧ v)  ≈⟨ sym $ ⊕-def _ _ ⟩
        y ⊕ v                ∎

      ⊕-identity : Identity ⊥ _⊕_
      ⊕-identity = ⊥⊕x=x , (\_ -> ⊕-comm _ _ ⟨ trans ⟩ ⊥⊕x=x _)
        where
        ⊥⊕x=x : forall x -> ⊥ ⊕ x ≈ x
        ⊥⊕x=x x = begin
          ⊥ ⊕ x                ≈⟨ ⊕-def _ _ ⟩
          (⊥ ∨ x) ∧ ¬ (⊥ ∧ x)  ≈⟨ helper (proj₁ ∨-identity _)
                                         (proj₁ ∧-zero _) ⟩
          x ∧ ¬ ⊥              ≈⟨ byDef ⟨ ∧-pres-≈ ⟩ ¬⊥=⊤ ⟩
          x ∧ ⊤                ≈⟨ proj₂ ∧-identity _ ⟩
          x                    ∎

      ⊕-inverse : Inverse ⊥ id _⊕_
      ⊕-inverse = x⊕x=⊥ , (\_ -> ⊕-comm _ _ ⟨ trans ⟩ x⊕x=⊥ _)
        where
        x⊕x=⊥ : forall x -> x ⊕ x ≈ ⊥
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
          x ∧ (y ⊕ z)                ≈⟨ byDef ⟨ ∧-pres-≈ ⟩ ⊕-def _ _ ⟩
          x ∧ ((y ∨ z) ∧ ¬ (y ∧ z))  ≈⟨ sym $ ∧-assoc _ _ _ ⟩
          (x ∧ (y ∨ z)) ∧ ¬ (y ∧ z)  ≈⟨ byDef ⟨ ∧-pres-≈ ⟩ deMorgan₁ _ _ ⟩
          (x ∧ (y ∨ z)) ∧
          (¬ y ∨ ¬ z)                ≈⟨ sym $ proj₁ ∨-identity _ ⟩
          ⊥ ∨
          ((x ∧ (y ∨ z)) ∧
           (¬ y ∨ ¬ z))              ≈⟨ lem₃ ⟨ ∨-pres-≈ ⟩ byDef ⟩
          ((x ∧ (y ∨ z)) ∧ ¬ x) ∨
          ((x ∧ (y ∨ z)) ∧
           (¬ y ∨ ¬ z))              ≈⟨ sym $ proj₁ ∧-∨-distrib _ _ _ ⟩
          (x ∧ (y ∨ z)) ∧
          (¬ x ∨ (¬ y ∨ ¬ z))        ≈⟨  byDef ⟨ ∧-pres-≈ ⟩
                                        (byDef ⟨ ∨-pres-≈ ⟩ sym (deMorgan₁ _ _)) ⟩
          (x ∧ (y ∨ z)) ∧
          (¬ x ∨ ¬ (y ∧ z))          ≈⟨ byDef ⟨ ∧-pres-≈ ⟩ sym (deMorgan₁ _ _) ⟩
            (x ∧ (y ∨ z)) ∧
          ¬ (x ∧ (y ∧ z))            ≈⟨ helper byDef lem₁ ⟩
            (x ∧ (y ∨ z)) ∧
          ¬ ((x ∧ y) ∧ (x ∧ z))      ≈⟨ proj₁ ∧-∨-distrib _ _ _ ⟨ ∧-pres-≈ ⟩
                                        byDef ⟩
            ((x ∧ y) ∨ (x ∧ z)) ∧
          ¬ ((x ∧ y) ∧ (x ∧ z))      ≈⟨ sym $ ⊕-def _ _ ⟩
          (x ∧ y) ⊕ (x ∧ z)          ∎
          where
          lem₂ = begin
            x ∧ (y ∧ z)  ≈⟨ sym $ ∧-assoc _ _ _ ⟩
            (x ∧ y) ∧ z  ≈⟨ ∧-comm _ _ ⟨ ∧-pres-≈ ⟩ byDef ⟩
            (y ∧ x) ∧ z  ≈⟨ ∧-assoc _ _ _ ⟩
            y ∧ (x ∧ z)  ∎

          lem₁ = begin
            x ∧ (y ∧ z)        ≈⟨ sym (∧-idempotent _) ⟨ ∧-pres-≈ ⟩ byDef ⟩
            (x ∧ x) ∧ (y ∧ z)  ≈⟨ ∧-assoc _ _ _ ⟩
            x ∧ (x ∧ (y ∧ z))  ≈⟨ byDef ⟨ ∧-pres-≈ ⟩ lem₂ ⟩
            x ∧ (y ∧ (x ∧ z))  ≈⟨ sym $ ∧-assoc _ _ _ ⟩
            (x ∧ y) ∧ (x ∧ z)  ∎

          lem₃ = begin
            ⊥                      ≈⟨ sym $ proj₂ ∧-zero _ ⟩
            (y ∨ z) ∧ ⊥            ≈⟨ byDef ⟨ ∧-pres-≈ ⟩ sym (proj₂ ∧-complement _) ⟩
            (y ∨ z) ∧ (x ∧ ¬ x)    ≈⟨ sym $ ∧-assoc _ _ _ ⟩
            ((y ∨ z) ∧ x) ∧ ¬ x    ≈⟨ ∧-comm _ _ ⟨ ∧-pres-≈ ⟩ byDef  ⟩
            (x ∧ (y ∨ z)) ∧ ¬ x    ∎

        distʳ : _∧_ DistributesOverʳ _⊕_
        distʳ x y z = begin
          (y ⊕ z) ∧ x        ≈⟨ ∧-comm _ _ ⟩
          x ∧ (y ⊕ z)        ≈⟨ distˡ _ _ _ ⟩
          (x ∧ y) ⊕ (x ∧ z)  ≈⟨ ∧-comm _ _ ⟨ ⊕-pres ⟩ ∧-comm _ _ ⟩
          (y ∧ x) ⊕ (z ∧ x)  ∎

      lemma₂ :  forall x y u v
             -> (x ∧ y) ∨ (u ∧ v) ≈
                ((x ∨ u) ∧ (y ∨ u)) ∧
                ((x ∨ v) ∧ (y ∨ v))
      lemma₂ x y u v = begin
          (x ∧ y) ∨ (u ∧ v)              ≈⟨ proj₁ ∨-∧-distrib _ _ _ ⟩
          ((x ∧ y) ∨ u) ∧ ((x ∧ y) ∨ v)  ≈⟨ proj₂ ∨-∧-distrib _ _ _
                                              ⟨ ∧-pres-≈ ⟩
                                            proj₂ ∨-∧-distrib _ _ _ ⟩
          ((x ∨ u) ∧ (y ∨ u)) ∧
          ((x ∨ v) ∧ (y ∨ v))            ∎

      ⊕-assoc : Associative _⊕_
      ⊕-assoc x y z = sym $ begin
        x ⊕ (y ⊕ z)                                ≈⟨ byDef ⟨ ⊕-pres ⟩ ⊕-def _ _ ⟩
        x ⊕ ((y ∨ z) ∧ ¬ (y ∧ z))                  ≈⟨ ⊕-def _ _ ⟩
          (x ∨ ((y ∨ z) ∧ ¬ (y ∧ z))) ∧
        ¬ (x ∧ ((y ∨ z) ∧ ¬ (y ∧ z)))              ≈⟨ lem₃ ⟨ ∧-pres-≈ ⟩ lem₄ ⟩
        (((x ∨ y) ∨ z) ∧ ((x ∨ ¬ y) ∨ ¬ z)) ∧
        (((¬ x ∨ ¬ y) ∨ z) ∧ ((¬ x ∨ y) ∨ ¬ z))    ≈⟨ ∧-assoc _ _ _ ⟩
        ((x ∨ y) ∨ z) ∧
        (((x ∨ ¬ y) ∨ ¬ z) ∧
         (((¬ x ∨ ¬ y) ∨ z) ∧ ((¬ x ∨ y) ∨ ¬ z)))  ≈⟨ byDef ⟨ ∧-pres-≈ ⟩ lem₅ ⟩
        ((x ∨ y) ∨ z) ∧
        (((¬ x ∨ ¬ y) ∨ z) ∧
         (((x ∨ ¬ y) ∨ ¬ z) ∧ ((¬ x ∨ y) ∨ ¬ z)))  ≈⟨ sym $ ∧-assoc _ _ _ ⟩
        (((x ∨ y) ∨ z) ∧ ((¬ x ∨ ¬ y) ∨ z)) ∧
        (((x ∨ ¬ y) ∨ ¬ z) ∧ ((¬ x ∨ y) ∨ ¬ z))    ≈⟨ lem₁ ⟨ ∧-pres-≈ ⟩ lem₂ ⟩
          (((x ∨ y) ∧ ¬ (x ∧ y)) ∨ z) ∧
        ¬ (((x ∨ y) ∧ ¬ (x ∧ y)) ∧ z)              ≈⟨ sym $ ⊕-def _ _ ⟩
        ((x ∨ y) ∧ ¬ (x ∧ y)) ⊕ z                  ≈⟨ sym $ ⊕-def _ _ ⟨ ⊕-pres ⟩ byDef ⟩
        (x ⊕ y) ⊕ z                                ∎
        where
        lem₁ = begin
          ((x ∨ y) ∨ z) ∧ ((¬ x ∨ ¬ y) ∨ z)  ≈⟨ sym $ proj₂ ∨-∧-distrib _ _ _ ⟩
          ((x ∨ y) ∧ (¬ x ∨ ¬ y)) ∨ z        ≈⟨ (byDef ⟨ ∧-pres-≈ ⟩ sym (deMorgan₁ _ _))
                                                      ⟨ ∨-pres-≈ ⟩ byDef ⟩
          ((x ∨ y) ∧ ¬ (x ∧ y)) ∨ z          ∎

        lem₂' = begin
          (x ∨ ¬ y) ∧ (¬ x ∨ y)              ≈⟨ sym $
                                                  proj₁ ∧-identity _
                                                    ⟨ ∧-pres-≈ ⟩
                                                  proj₂ ∧-identity _ ⟩
          (⊤ ∧ (x ∨ ¬ y)) ∧ ((¬ x ∨ y) ∧ ⊤)  ≈⟨ sym $
                                                  (proj₁ ∨-complement _ ⟨ ∧-pres-≈ ⟩ ∨-comm _ _)
                                                    ⟨ ∧-pres-≈ ⟩
                                                  (byDef ⟨ ∧-pres-≈ ⟩ proj₁ ∨-complement _) ⟩
          ((¬ x ∨ x) ∧ (¬ y ∨ x)) ∧
          ((¬ x ∨ y) ∧ (¬ y ∨ y))            ≈⟨ sym $ lemma₂ _ _ _ _ ⟩
          (¬ x ∧ ¬ y) ∨ (x ∧ y)              ≈⟨ sym $ deMorgan₂ _ _ ⟨ ∨-pres-≈ ⟩ ¬-involutive _ ⟩
          ¬ (x ∨ y) ∨ ¬ ¬ (x ∧ y)            ≈⟨ sym (deMorgan₁ _ _) ⟩
          ¬ ((x ∨ y) ∧ ¬ (x ∧ y))            ∎

        lem₂ = begin
          ((x ∨ ¬ y) ∨ ¬ z) ∧ ((¬ x ∨ y) ∨ ¬ z)  ≈⟨ sym $ proj₂ ∨-∧-distrib _ _ _ ⟩
          ((x ∨ ¬ y) ∧ (¬ x ∨ y)) ∨ ¬ z          ≈⟨ lem₂' ⟨ ∨-pres-≈ ⟩ byDef ⟩
          ¬ ((x ∨ y) ∧ ¬ (x ∧ y)) ∨ ¬ z          ≈⟨ sym $ deMorgan₁ _ _ ⟩
          ¬ (((x ∨ y) ∧ ¬ (x ∧ y)) ∧ z)          ∎

        lem₃ = begin
          x ∨ ((y ∨ z) ∧ ¬ (y ∧ z))          ≈⟨ byDef ⟨ ∨-pres-≈ ⟩
                                                  (byDef ⟨ ∧-pres-≈ ⟩ deMorgan₁ _ _) ⟩
          x ∨ ((y ∨ z) ∧ (¬ y ∨ ¬ z))        ≈⟨ proj₁ ∨-∧-distrib _ _ _ ⟩
          (x ∨ (y ∨ z)) ∧ (x ∨ (¬ y ∨ ¬ z))  ≈⟨ sym (∨-assoc _ _ _) ⟨ ∧-pres-≈ ⟩
                                                sym (∨-assoc _ _ _) ⟩
          ((x ∨ y) ∨ z) ∧ ((x ∨ ¬ y) ∨ ¬ z)  ∎

        lem₄' = begin
          ¬ ((y ∨ z) ∧ ¬ (y ∧ z))    ≈⟨ deMorgan₁ _ _ ⟩
          ¬ (y ∨ z) ∨ ¬ ¬ (y ∧ z)    ≈⟨ deMorgan₂ _ _ ⟨ ∨-pres-≈ ⟩ ¬-involutive _ ⟩
          (¬ y ∧ ¬ z) ∨ (y ∧ z)      ≈⟨ lemma₂ _ _ _ _ ⟩
          ((¬ y ∨ y) ∧ (¬ z ∨ y)) ∧
          ((¬ y ∨ z) ∧ (¬ z ∨ z))    ≈⟨ (proj₁ ∨-complement _ ⟨ ∧-pres-≈ ⟩ ∨-comm _ _)
                                          ⟨ ∧-pres-≈ ⟩
                                        (byDef ⟨ ∧-pres-≈ ⟩ proj₁ ∨-complement _) ⟩
          (⊤ ∧ (y ∨ ¬ z)) ∧
          ((¬ y ∨ z) ∧ ⊤)            ≈⟨ proj₁ ∧-identity _ ⟨ ∧-pres-≈ ⟩
                                        proj₂ ∧-identity _ ⟩
          (y ∨ ¬ z) ∧ (¬ y ∨ z)      ∎

        lem₄ = begin
          ¬ (x ∧ ((y ∨ z) ∧ ¬ (y ∧ z)))  ≈⟨ deMorgan₁ _ _ ⟩
          ¬ x ∨ ¬ ((y ∨ z) ∧ ¬ (y ∧ z))  ≈⟨ byDef ⟨ ∨-pres-≈ ⟩ lem₄' ⟩
          ¬ x ∨ ((y ∨ ¬ z) ∧ (¬ y ∨ z))  ≈⟨ proj₁ ∨-∧-distrib _ _ _ ⟩
          (¬ x ∨ (y     ∨ ¬ z)) ∧
          (¬ x ∨ (¬ y ∨ z))              ≈⟨ sym (∨-assoc _ _ _) ⟨ ∧-pres-≈ ⟩
                                            sym (∨-assoc _ _ _) ⟩
          ((¬ x ∨ y)     ∨ ¬ z) ∧
          ((¬ x ∨ ¬ y) ∨ z)              ≈⟨ ∧-comm _ _ ⟩
          ((¬ x ∨ ¬ y) ∨ z) ∧
          ((¬ x ∨ y)     ∨ ¬ z)          ∎

        lem₅ = begin
          ((x ∨ ¬ y) ∨ ¬ z) ∧
          (((¬ x ∨ ¬ y) ∨ z) ∧ ((¬ x ∨ y) ∨ ¬ z))    ≈⟨ sym $ ∧-assoc _ _ _ ⟩
          (((x ∨ ¬ y) ∨ ¬ z) ∧ ((¬ x ∨ ¬ y) ∨ z)) ∧
          ((¬ x ∨ y) ∨ ¬ z)                          ≈⟨ ∧-comm _ _ ⟨ ∧-pres-≈ ⟩ byDef ⟩
          (((¬ x ∨ ¬ y) ∨ z) ∧ ((x ∨ ¬ y) ∨ ¬ z)) ∧
          ((¬ x ∨ y) ∨ ¬ z)                          ≈⟨ ∧-assoc _ _ _ ⟩
          ((¬ x ∨ ¬ y) ∨ z) ∧
          (((x ∨ ¬ y) ∨ ¬ z) ∧ ((¬ x ∨ y) ∨ ¬ z))    ∎

    isCommutativeRing : IsCommutativeRing _⊕_ _∧_ id ⊥ ⊤
    isCommutativeRing = record
      { isRing = record
        { +-isAbelianGroup = record
          { isGroup = record
            { isMonoid = record
              { isSemigroup = record
                { assoc    = ⊕-assoc
                ; •-pres-≈ = ⊕-pres
                }
              ; identity = ⊕-identity
              }
            ; inverse   = ⊕-inverse
            ; ⁻¹-pres-≈ = id
            }
          ; comm = ⊕-comm
          }
        ; *-isMonoid = record
          { isSemigroup = record
            { assoc    = ∧-assoc
            ; •-pres-≈ = ∧-pres-≈
            }
          ; identity = ∧-identity
          }
        ; distrib = distrib-∧-⊕
        }
      ; *-comm = ∧-comm
      }

  commutativeRing : CommutativeRing
  commutativeRing = record
    { setoid            = setoid
    ; _+_               = _⊕_
    ; _*_               = _∧_
    ; -_                = id
    ; 0#                = ⊥
    ; 1#                = ⊤
    ; isCommutativeRing = isCommutativeRing
    }

infixl 6 _⊕_

_⊕_ : Op₂
x ⊕ y = (x ∨ y) ∧ ¬ (x ∧ y)

module DefaultXorRing = XorRing _⊕_ (\_ _ -> byDef)

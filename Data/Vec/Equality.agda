------------------------------------------------------------------------
-- Semi-heterogeneous vector equality
------------------------------------------------------------------------

module Data.Vec.Equality {a : Set} where

open import Data.Vec
open import Data.Nat
open import Data.Function
import Relation.Binary.PropositionalEquality as PropEq
open PropEq using (_≡_)
import Relation.Binary.HeterogeneousEquality as HetEq
open HetEq using (_≅_)

infix 4 _≈_

data _≈_ : ∀ {n¹} → Vec a n¹ →
           ∀ {n²} → Vec a n² → Set where
  []-cong  : [] ≈ []
  _∷-cong_ : ∀ {x¹ n¹} {xs¹ : Vec a n¹}
               {x² n²} {xs² : Vec a n²}
             (x¹≡x² : x¹ ≡ x²) (xs¹≈xs² : xs¹ ≈ xs²) →
             x¹ ∷ xs¹ ≈ x² ∷ xs²

length-equal : ∀ {n¹} {xs¹ : Vec a n¹}
                 {n²} {xs² : Vec a n²} →
               xs¹ ≈ xs² → n¹ ≡ n²
length-equal []-cong        = PropEq.refl
length-equal (_ ∷-cong eq₂) = PropEq.cong suc $ length-equal eq₂

to-≅ : ∀ {n¹} {xs¹ : Vec a n¹}
         {n²} {xs² : Vec a n²} →
       xs¹ ≈ xs² → xs¹ ≅ xs²
to-≅ []-cong                  = HetEq.refl
to-≅ (PropEq.refl ∷-cong eq₂) with length-equal eq₂
... | PropEq.refl = HetEq.cong (_∷_ _) $ to-≅ eq₂

refl : ∀ {n} (xs : Vec a n) → xs ≈ xs
refl []       = []-cong
refl (x ∷ xs) = PropEq.refl ∷-cong refl xs

_++-cong_ : ∀ {n₁¹ n₂¹} {xs₁¹ : Vec a n₁¹} {xs₂¹ : Vec a n₂¹}
              {n₁² n₂²} {xs₁² : Vec a n₁²} {xs₂² : Vec a n₂²} →
              xs₁¹ ≈ xs₁² → xs₂¹ ≈ xs₂² →
              xs₁¹ ++ xs₂¹ ≈ xs₁² ++ xs₂²
[]-cong          ++-cong eq₃ = eq₃
(eq₁ ∷-cong eq₂) ++-cong eq₃ = eq₁ ∷-cong (eq₂ ++-cong eq₃)

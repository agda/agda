------------------------------------------------------------------------
-- Semi-heterogeneous vector equality
------------------------------------------------------------------------

module Data.Vec.Equality {a : Set} where

open import Data.Vec
open import Data.Nat
open import Data.Function
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.HeterogeneousEquality

infix 4 _≈-Vec_

data _≈-Vec_ :  forall {n¹} -> Vec a n¹
             -> forall {n²} -> Vec a n²
             -> Set where
  []-cong  :  [] ≈-Vec []
  _∷-cong_ :  forall {x¹ n¹} {xs¹ : Vec a n¹}
                     {x² n²} {xs² : Vec a n²}
           -> x¹ ≡ x² -> xs¹ ≈-Vec xs²
           -> x¹ ∷ xs¹ ≈-Vec x² ∷ xs²

length-equal :  forall {n¹} {xs¹ : Vec a n¹}
                       {n²} {xs² : Vec a n²}
             -> xs¹ ≈-Vec xs² -> n¹ ≡ n²
length-equal []-cong        = ≡-refl
length-equal (_ ∷-cong eq₂) = ≡-cong suc $ length-equal eq₂

to-≅ :  forall {n¹} {xs¹ : Vec a n¹}
               {n²} {xs² : Vec a n²}
     -> xs¹ ≈-Vec xs² -> xs¹ ≅ xs²
to-≅ []-cong             = ≅-refl
to-≅ (≡-refl ∷-cong eq₂) with length-equal eq₂
...                      | ≡-refl = ≅-cong (_∷_ _) $ to-≅ eq₂

Vec-refl : forall {n} (xs : Vec a n) -> xs ≈-Vec xs
Vec-refl []       = []-cong
Vec-refl (x ∷ xs) = ≡-refl ∷-cong Vec-refl xs

_++-cong_
  :  forall {n₁¹ n₂¹} {xs₁¹ : Vec a n₁¹} {xs₂¹ : Vec a n₂¹}
            {n₁² n₂²} {xs₁² : Vec a n₁²} {xs₂² : Vec a n₂²}
  -> xs₁¹ ≈-Vec xs₁² -> xs₂¹ ≈-Vec xs₂²
  -> xs₁¹ ++ xs₂¹ ≈-Vec xs₁² ++ xs₂²
[]-cong          ++-cong eq₃ = eq₃
(eq₁ ∷-cong eq₂) ++-cong eq₃ = eq₁ ∷-cong (eq₂ ++-cong eq₃)

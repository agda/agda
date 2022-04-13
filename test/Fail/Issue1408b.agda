{-# OPTIONS --cubical-compatible #-}
open import Common.Prelude
open import Common.Equality
open import Common.Product

data _≅_ {A : Set} (a : A) : {B : Set} (b : B) → Set₁ where
  refl : a ≅ a

data D : Bool → Set where
  x  : D true
  y  : D false

P : Set -> Set₁
P S = Σ S (\s → s ≅ x)

pbool : P (D true)
pbool = _ , refl

¬pfin : P (D false) → ⊥
¬pfin (y , ())

{-# OPTIONS --cubical #-}
module TranspComputing where

open import Agda.Builtin.Cubical.Path
open import Agda.Primitive.Cubical
open import Agda.Builtin.List


transpList : ∀ (φ : I) (A : Set) x xs → primTransp (λ _ → List A) φ (x ∷ xs) ≡ (primTransp (λ i → A) φ x ∷ primTransp (λ i → List A) φ xs)
transpList φ A x xs = \ _ → primTransp (λ _ → List A) φ (x ∷ xs)


data S¹ : Set where
  base : S¹
  loop : base ≡ base

-- This should be refl.
transpS¹ : ∀ (φ : I) (u0 : S¹) → primTransp (λ _ → S¹) φ u0 ≡ u0
transpS¹ φ u0 = \ _ →  u0

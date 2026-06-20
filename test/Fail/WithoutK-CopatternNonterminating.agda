{-# OPTIONS --without-K #-}
module WithoutK-CopatternNonterminating where

open import Agda.Primitive using (Level; lsuc)

data ⊥ : Set where

data _≡_ {ℓ} {A : Set ℓ} (a : A) : A → Set ℓ where
  refl : a ≡ a

mutual
  data WOne : Set where
    wrap : FOne → WOne
  FOne : Set
  FOne = ⊥ → WOne

postulate iso : WOne ≡ FOne

record R : Set₁ where
  field bad : (X : Set) → WOne ≡ X → X → ⊥
open R

-- Must be rejected by the termination checker.
r : R
r .bad .WOne refl (wrap f) = r .bad FOne iso f

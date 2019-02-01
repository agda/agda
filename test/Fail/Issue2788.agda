module _ where

open import Agda.Primitive

postulate
  Equiv : ∀ {a b} → (A : Set a) (B : Set b) → Set (a ⊔ b)

{-# BUILTIN EQUIV Equiv #-}

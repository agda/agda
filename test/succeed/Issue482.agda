
module Issue482 where

open import Common.Level using (_⊔_)

postulate
  P      : ∀ a b → Set a → Set b → Set (a ⊔ b)
  F      : ∀ ℓ → Set ℓ
  p      : ∀ a (A : Set a) → P a a A (F a)
  Q      : ∀ a → Set a → ∀ b → Set (a ⊔ b)
  P-to-Q : ∀ a b (A : Set a) (B : Set b) → P a b A B → Q a A b

q : ∀ a (A : Set a) → Q a A _
q a A = P-to-Q _ _ _ _ (p _ _)

{-

  There was a bug in the level constraint solver that looks
  at pairs of constraints.

-}
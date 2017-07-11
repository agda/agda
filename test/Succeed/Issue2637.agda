-- Andreas, 2017-07-11, issue #2637, reported by nad.
--
-- This error was triggered by a meta m in a constraint UnBlock m
-- which is solved to infinity by the size solver.

-- The constraint printer did not expect such a situation
-- and crashed when printing the UnBlock constraint.

{-# OPTIONS --allow-unsolved-metas #-}

module _ (Z : Set) where

open import Common.Size
open import Common.Product

postulate
  map    : (A B C : Set) → (A → C) → A × B → C × B
  I      : Set
  P      : I → Set
  Q      : Size → I → Set
  f      : I → I
  lemma₁ : (R : I → Set) → (∀ x → R (f x) → R x) → ∀ x → R x → R (f x)
  lemma₂ : ∀ i x → Q i (f x) → Q i x

works : ∀ i x → Q i (f x) × P x → Q i (f (f x)) × P x
works i x = map
  (Q i (f x))
  (P x)
  (Q i (f (f x)))
  (lemma₁ (Q i) (λ y → lemma₂ i y) (f x))

-- Replacing any underscore by its solution or parts of its solution
-- makes the internal error disappear.

lemma₃ : ∀ i x → Q i (f x) × P x → Q i (f (f x)) × P x
lemma₃ i x = map
  (Q _ _)
  (P x)
  (Q _ (f (f x)))
  (lemma₁ _ (λ y → lemma₂ _ _) _)

-- Andreas, 2024-05-10, issue #7193 by dolio

{-# OPTIONS --no-irrelevant-projections #-}  -- default, but for clarity

record ⊤ : Set where

record TSquash (A : Set) : Set where
  field
    .extract : ⊤ → A

  .tflat : ⊤ → A
  tflat = extract

-- Expected error:
--
-- Projection  extract  is irrelevant.
-- Turn on option --irrelevant-projections to use it (unsafe).
-- when checking that the expression extract has type ⊤ → A

open TSquash

.flat : ∀{A} → .A → A
flat a = tflat (λ where .extract _ → a) _

-- Should not pass without --irrelevant-projections

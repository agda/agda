module Issue852 where

open import Common.Level

const : ∀ {a b} {A : Set a} {B : Set b} → A → B → A
const x = λ _ → x
{-# NOINLINE const #-}

ℓ : Level
ℓ = const lzero (Set ℓ)

ℓ′ : Level
ℓ′ = const lzero (Set ℓ′)

-- Error message using Agda 2.3.2 (the batch-mode command, not the
-- Emacs interface):
--
--   Termination checking failed for the following functions:
--     ℓ, ℓ′
--   Problematic calls:
--     ℓ
--     ℓ (at [...])
--     ℓ′
--     ℓ′
--       (at [...])
--
-- With the current development version of Agda:
--
--   Termination checking failed for the following functions:
--     ℓ, ℓ′
--   Problematic calls:
--     ℓ
--     ℓ (at [...])
--     ℓ′
--       (at [...])

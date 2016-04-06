module Issue1760d where

-- Skipping a new-style mutual block: Anywhere before the declaration or
-- the definition of a data/record in the block (case: record).
{-# NO_POSITIVITY_CHECK #-}
record U₁ : Set
data D₁   : Set

record U₁ where
  field ap : U₁ → U₁

data D₁ where
  lam : (D₁ → D₁) → D₁

-- Skipping a new-style mutual block: Anywhere before the declaration or
-- the definition of a data/record in the block (case: data).
record U₂ : Set
data D₂   : Set

record U₂ where
  field ap : U₂ → U₂

{-# NO_POSITIVITY_CHECK #-}
data D₂ where
  lam : (D₂ → D₂) → D₂

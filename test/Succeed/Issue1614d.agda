-- New NO_POSITIVITY_CHECK pragma for data definitions and mutual
-- blocks

-- Skipping a new-style mutual block: Anywhere before the declaration
-- or the definition of a data type in the block (case: before first
-- declaration).

{-# NO_POSITIVITY_CHECK #-}
data Cheat₁ : Set
data Oops₁  : Set

data Cheat₁ where
  cheat₁ : Oops₁ → Cheat₁

data Oops₁ where
  oops₁ : (Cheat₁ → Cheat₁) → Oops₁

-- Skipping a new-style mutual block: Anywhere before the declaration
-- or the definition of a data type in the block (case: before some
-- definition).

data Cheat₂ : Set
data Oops₂  : Set

data Cheat₂ where
  cheat₂ : Oops₂ → Cheat₂

{-# NO_POSITIVITY_CHECK #-}
data Oops₂ where
  oops₂ : (Cheat₂ → Cheat₂) → Oops₂

-- New NO_POSITIVITY_CHECK pragma for data definitions and mutual
-- blocks

-- Skipping a new-style mutual block: Before the declaration and the
-- definition of the first data type.

{-# NO_POSITIVITY_CHECK #-}
data Cheat₁ : Set
data Oops₁  : Set

{-# NO_POSITIVITY_CHECK #-}
data Cheat₁ where
  cheat₁ : Oops₁ → Cheat₁

data Oops₁ where
  oops₁ : (Cheat₁ → Cheat₁) → Oops₁

-- Skipping a new-style mutual block: Before the declaration and
-- the definition of the second data type.

data Cheat₂ : Set
{-# NO_POSITIVITY_CHECK #-}
data Oops₂  : Set

data Cheat₂ where
  cheat₂ : Oops₂ → Cheat₂

{-# NO_POSITIVITY_CHECK #-}
data Oops₂ where
  oops₂ : (Cheat₂ → Cheat₂) → Oops₂

-- New NO_POSITIVITY_CHECK pragma for data definitions and mutual
-- blocks

-- Skipping a new-style mutual block: Before the declaration and the
-- definition of the first data type.

-- ASR TODO (27 December 2015): Use an example with mutually
-- non-strictly positive data types.
{-# NO_POSITIVITY_CHECK #-}
data Tree₁ (A : Set) : Set
data Bad₁ : Set

{-# NO_POSITIVITY_CHECK #-}
data Tree₁ A where
  leaf₁ : Tree₁ A
  node₁ : (A → Tree₁ A) → Tree₁ A

data Bad₁ where
  bad₁ : Tree₁ Bad₁ → Bad₁

-- Skipping a new-style mutual block: Before the declaration and
-- the definition of the second data type.

-- ASR TODO (27 December 2015): Use an example with mutually
-- non-strictly positive data types.
data Tree₂ (A : Set) : Set
{-# NO_POSITIVITY_CHECK #-}
data Bad₂ : Set

data Tree₂ A where
  leaf₂ : Tree₂ A
  node₂ : (A → Tree₂ A) → Tree₂ A

{-# NO_POSITIVITY_CHECK #-}
data Bad₂ where
  bad₂ : Tree₂ Bad₂ → Bad₂

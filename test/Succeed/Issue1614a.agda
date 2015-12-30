-- New NO_POSITIVITY_CHECK pragma for data definitions and mutual
-- blocks

-- Skipping a single data definition.
{-# NO_POSITIVITY_CHECK #-}
data D : Set where
  lam : (D → D) → D

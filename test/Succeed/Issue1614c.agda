-- New NO_POSITIVITY_CHECK pragma for data definitions and mutual
-- blocks

-- Skipping an old-style mutual block: Before the `mutual` keyword.
{-# NO_POSITIVITY_CHECK #-}
mutual
  data D : Set where
    lam : (D → D) → D

  data NSPos (A : Set) : Set where
    c : ((NSPos A → A) → NSPos A) → NSPos A

-- New NO_POSITIVITY_CHECK pragma for data definitions and mutual
-- blocks

-- Skipping an old-style mutual block: Somewhere within a `mutual`
-- block before a data definition.
mutual
  data D : Set where
    lam : (D → D) → D

  {-# NO_POSITIVITY_CHECK #-}
  data NSPos (A : Set) : Set where
    c : ((NSPos A → A) → NSPos A) → NSPos A

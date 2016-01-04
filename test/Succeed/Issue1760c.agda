module Issue1760c where

-- Skipping an old-style mutual block: Before the `mutual` keyword.
{-# NO_POSITIVITY_CHECK #-}
mutual
  data D : Set where
    lam : (D → D) → D

  record U : Set where
    field ap : U → U

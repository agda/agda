module Issue1760b where

-- Skipping an old-style mutual block: Somewhere within a `mutual`
-- block before a record definition.
mutual
  data D : Set where
    lam : (D → D) → D

  {-# NO_POSITIVITY_CHECK #-}
  record U : Set where
    field ap : U → U

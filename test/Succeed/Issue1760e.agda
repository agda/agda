module Issue1760e where

-- Skipping a single record definition in a private block.
private
  {-# NO_POSITIVITY_CHECK #-}
  record U : Set where
    field ap : U → U

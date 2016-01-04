module Issue1760f where

-- Skipping a single record definition in an abstract block.
abstract
  {-# NO_POSITIVITY_CHECK #-}
  record U : Set where
    field ap : U → U

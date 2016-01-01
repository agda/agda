module Issue1760a where

-- Skipping a single record definition.
{-# NO_POSITIVITY_CHECK #-}
record U : Set where
  field ap : U → U

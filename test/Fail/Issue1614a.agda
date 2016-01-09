-- The NO_POSITIVITY_CHECK pragma is not allowed in safe mode.

module Issue1614a where

{-# NO_POSITIVITY_CHECK #-}
data D : Set where
  lam : (D → D) → D

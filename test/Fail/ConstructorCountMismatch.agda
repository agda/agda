-- Andreas, 2024-07-22
-- Trigger error GHCBackend.ConstructorCountMismatch

data D : Set where
  d1 d2 : D

{-# FOREIGN GHC data D = D1 #-}
{-# COMPILE GHC D = data D (D1) #-}

-- Expected compilation error:
-- D has 2 constructors, but only 1 Haskell constructor is given [D1]

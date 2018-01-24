
postulate
  F : Set₁ → Set₁

record R : Set₁ where
  field
    f : F Set

{-# COMPILE GHC F = \ _ -> () #-}

{-# FOREIGN GHC data D = C () #-}
{-# COMPILE GHC R = data D (C) #-}


{-# NO_POSITIVITY_CHECK #-}
data D : Set
data D where
  d : (D → D) → D

data E : Set
{-# NO_POSITIVITY_CHECK #-}
data E where
  e : (E → E) → E

{-# NO_POSITIVITY_CHECK #-}
data F : Set
{-# NO_POSITIVITY_CHECK #-}
data F where
  e : (F → F) → F

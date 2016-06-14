postulate
  F : Set → Set

{-# POLARITY F * #-}

data D : Set where
  d : F D → D

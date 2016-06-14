module _ where

module _ (A : Set) where

  postulate
    F : Set₁ → Set

  {-# POLARITY F ++ #-}

data D : Set where
  d : F D Set → D

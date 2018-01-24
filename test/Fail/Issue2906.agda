
data D : Set where
  zero : D
  suc  : D → D

postulate
  f : D → D

{-# COMPILE GHC f = \ x -> x #-}

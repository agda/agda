{-# OPTIONS --erasure #-}

data @0 D : Set

data D where
  c : D

_ : D
_ = c

{-# OPTIONS --erasure #-}

data D : Set where
  @0 c : D

postulate
  P : D → Set
  p : (x : D) → P x

bad : P c
bad = p _

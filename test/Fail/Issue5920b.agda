{-# OPTIONS --without-K #-}

data D : Set where
  @0 c : D

data P : D → Set where
  d : P c

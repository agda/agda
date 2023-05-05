{-# OPTIONS --erasure #-}

postulate
  I : Set

data Box (A : Set) : Set where
  [_] : A → Box A

variable
  @0 i : I
  @0 b : Box I

data D : @0 Box I → Set where
  d : D [ i ] → D [ i ]

variable
  @0 x : D b

data P : @0 D b → Set where
  p : P (d x)

works : ∀ {i} {@0 x : D [ i ]} → P (d x)
works = p

fails : ∀ {@0 i} {@0 x : D [ i ]} → P (d x)
fails = p

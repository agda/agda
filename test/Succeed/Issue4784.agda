{-# OPTIONS --without-K #-}
postulate
  A : Set
  B : A → Set

@0 T : Set
T = (@0 x : A) → B x

{-# OPTIONS --cubical-compatible #-}
postulate
  A : Set
  B : A → Set

T = (@0 x : A) → B x

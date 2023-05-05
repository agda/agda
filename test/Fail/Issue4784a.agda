{-# OPTIONS --cubical-compatible --erasure #-}

postulate
  A : Set
  B : A → Set

T = (@0 x : A) → B x

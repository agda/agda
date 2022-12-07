{-# OPTIONS --erasure #-}

postulate
  A : Set
  B : A → Set

@0 T : _
T = (@0 x : A) → B x

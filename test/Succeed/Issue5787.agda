{-# OPTIONS --erasure #-}

postulate
  A B : Set
  f : @0 {{A}} → B

g : @0 {{A}} → B
g = f

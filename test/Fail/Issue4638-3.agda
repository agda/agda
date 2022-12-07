{-# OPTIONS --erasure #-}

data D : Set where
  @0 c : D

-- The following definition should be rejected. Matching on an erased
-- constructor in an *erased* position should not on its own make it
-- possible to use erased definitions in the right-hand side.

f : @0 D → D
f c = c

x : D
x = f c

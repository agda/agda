{-# OPTIONS --prop #-}

{-# TERMINATING #-}
makeloop : {P : Prop} → P → P
makeloop p = makeloop p

postulate
  P : Prop
  p : P
  Q : P → Set

record X : Set where
  field
    f : Q (makeloop p)

data Y : Set where
  f : Q (makeloop p) → Y

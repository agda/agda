{-# OPTIONS --prop --show-irrelevant #-}

postulate
  P : Prop
  p : P
  A : P → Set
  f : {x : P} → A x

test : A p
test = f

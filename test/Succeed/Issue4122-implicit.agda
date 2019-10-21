{-# OPTIONS --prop --show-irrelevant -v tc.conv:50 #-}

postulate
  P : Prop
  p : P
  A : P → Set
  f : {x : P} → A x

test : A p
test = f

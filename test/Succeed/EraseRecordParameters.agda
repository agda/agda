{-# OPTIONS --erase-record-parameters #-}

postulate A : Set
postulate a : A

record R (x : A) : Set where
  y : A
  y = a

f : (@0 x : A) → R x → A
f x r = R.y {x} r

open R {{...}}

g : {@0 x : A} → {{R x}} → A
g = y

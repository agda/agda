postulate
  H I : Set → Set → Set
  !_  : Set → Set
  X   : Set

infix 1 !_
infix 0 H

syntax H X Y = X , Y
syntax I X Y = Y , X

Foo : Set
Foo = ! X , X

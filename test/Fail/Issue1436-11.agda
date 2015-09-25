postulate
  H I : Set → Set → Set
  !_  : Set → Set
  X   : Set

infix 1 !_
infix 0 H

syntax H X Y = X , Y
syntax I X Y = Y , X

-- This parsed when default fixity was 'unrelated', but with
-- an actual default fixity (of any strength) in place it really
-- should not.
Foo : Set
Foo = ! X , X

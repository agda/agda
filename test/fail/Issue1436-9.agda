postulate
  F G : (Set → Set) → Set
  !_  : Set → Set

infix 2 F
infix 1 !_

syntax F (λ X → Y) = X , Y
syntax G (λ X → Y) = Y , X

-- This parsed when default fixity was 'unrelated', but with
-- an actual default fixity (of any strength) in place it really
-- should not.
Foo : Set
Foo = ! X , X

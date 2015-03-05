postulate
  F G : (Set → Set) → Set
  !_  : Set → Set

infix 2 F
infix 1 !_

syntax F (λ X → Y) = X , Y
syntax G (λ X → Y) = Y , X

Foo : Set
Foo = ! X , X

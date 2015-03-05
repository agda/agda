postulate
  F  : (Set → Set) → Set
  H  : Set → Set → Set
  !_ : Set → Set
  X  : Set

infix 2 F
infix 1 !_

syntax F (λ X → Y) = X , Y
syntax H X Y       = X , Y

Foo : Set
Foo = ! X , X

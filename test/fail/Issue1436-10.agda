postulate
  F  : (Set → Set) → Set
  H  : Set → Set → Set
  !_ : Set → Set
  X  : Set

infix 2 F
infix 1 !_

syntax F (λ X → Y) = X , Y
syntax H X Y       = X , Y

-- This parsed when default fixity was 'unrelated', but with
-- an actual default fixity (of any strength) in place it really
-- should not.
Foo : Set
Foo = ! X , X

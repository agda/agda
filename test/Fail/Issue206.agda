
module Issue206 where

postulate
  I : Set
  P : I → Set
  i : I
  Q : P i → Set

Foo : (p : P i) → Q p → Set₁
Foo p q with i
Foo p q | i′ = Set

-- Now better error message:
-- Issue206.agda:11,1-19
-- w != i of type I
-- when checking that the type of the generated with function
-- (w : I) (p : P w) (q : Q p) → Set₁ is well-formed

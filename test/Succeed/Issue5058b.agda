
module _ where

postulate
  I : Set
  D : I → Set
  E : ∀ {i} → D i → Set

variable
  A : Set
  x : A

-- foo : {@0 i : I} {x : D i} → E x → I
foo : E x → I
foo {i = i} _ = i -- error: Variable i is declared erased

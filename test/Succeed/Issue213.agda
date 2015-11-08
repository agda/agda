
module Issue213 where

postulate
  Prod : Set → Set → Set
  A    : Set

Foo : Set
Foo = let infixr 3 _×_
          _×_ : Set → Set → Set
          _×_ = Prod
      in A × A × A


Type-of : {A : Set} → A → Set
Type-of {A = A} _ = A

module _ (A : Set) where

  Foo : A → Set
  Foo a with Type-of a
  ... | B = B

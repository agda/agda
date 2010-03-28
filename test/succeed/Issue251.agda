module Issue251 where

record Foo : Set₁ where
  field
    A : Set
    B : Set

foo : Set → Set → Foo
foo = λ A B → record {A = A; B = B}

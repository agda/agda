record R : Set₁ where
  field
    A : Set

  B : Set
  B = A

  field
    C : Set

  D : Set
  D = A → B → C

module RecordFieldAndModules where

record R1 : Set₁ where
  field
    A : Set
    B : A → Set

record R2 : Set₂ where
  field
    X : Set
    r1 : X → R1

  module M1 {x} = R1 (r1 x)

  field
    a : ∀ {x} → R1.A (r1 x)

  A : X → Set
  A x = R1.A (r1 x)

  B : ∀ {x} → A x → Set
  B x = M1.B x

  field
    foo : ∀ {x} (a : A x) → B a

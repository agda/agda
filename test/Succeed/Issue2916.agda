
mutual

  record R (A : Set) : Set where
    inductive
    field
      f₁ : A
      f₂ : R′ A

  record R′ (A : Set) : Set where
    inductive
    field
      f : R A

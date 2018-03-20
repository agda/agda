record R (A B : Set) : Set where
  constructor c₁
  field
    x : A

mutual

  T : Set
  T = R D T

  data D : Set where
    c₂ : T → D

f : T → Set
f (c₁ (c₂ x)) = f x

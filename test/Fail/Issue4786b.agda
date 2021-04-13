record R (A : Set) : Set where
  constructor c₂
  field
    f : A → A

open module R′ (A : Set) (r : R A) = R {A = A} r
  renaming (f to f′)

_ : (@0 A : Set) → R A → A → A
_ = λ A → f′ {A = A}

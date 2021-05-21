record R (A : Set) : Set where
  constructor c₂
  field
    f : A → A

  g : A → A
  g x = f (f x)

open R public

_ : (@0 A : Set) → R A → A → A
_ = λ A → g {A = A}

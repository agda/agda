
record R (A : Set) : Set where
  field
    x : A

works : (@0 A : Set) → R A → A
works _ record{ x = x } = x

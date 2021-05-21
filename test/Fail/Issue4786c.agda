record R (A : Set) : Set where
  field
    f : A → A

open module R′ (@0 A : Set) (r : R A) = R {A = A} r

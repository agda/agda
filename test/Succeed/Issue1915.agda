
record Pointed (A : Set) : Set where
  field
    point : A

point : {A : Set} ⦃ p : Pointed A ⦄ → A
point ⦃ p = p ⦄ = Pointed.point p

record R : Set₁ where
  field
    A : Set
    instance
      is-pointed : Pointed A

postulate
  r : R

open R r

x : R.A r
x = point

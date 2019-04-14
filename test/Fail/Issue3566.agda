postulate
  A : Set
  P : A → Set
  p : (a : A) → P a

record R : Set where
  field
    a : A
  b : P _
  b = p a

test : A
test = R.b

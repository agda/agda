it : {X : Set} → {{X}} → X
it {{x}} = x

postulate
  A : Set
  a : A

opaque
  B : Set
  B = A

  instance
    b : B
    b = a

works : B
works = it

opaque
  unfolding B

  fails : B
  fails = it

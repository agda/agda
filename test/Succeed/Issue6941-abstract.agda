it : {X : Set} → {{X}} → X
it {{x}} = x

postulate
  A : Set
  a : A

abstract
  B : Set
  B = A

  instance
    b : B
    b = a

works : B
works = it

abstract
  fails : B
  fails = it

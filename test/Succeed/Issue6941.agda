it : {X : Set} → {{X}} → X
it {{x}} = x

postulate
  A : Set
  a : A

module Opaque where

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

module Abstract where

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

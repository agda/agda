
postulate
  A : Set
  a : A

record B : Set where
  constructor i
  field b : A
open B

data D : (X : Set) → X → Set where
  c : D B (record { b = a })

accepted : (X : Set) (x : X) → D X x → Set
accepted .B (i a) c = A

rejected : (X : Set) (x : X) → D X x → Set
rejected .B (record { b = a }) c = A

-- WAS:
-- I'm not sure if there should be a case for the constructor c,
-- because I get stuck when trying to solve the following unification
-- problems (inferred index ≟ expected index):
--   B ≟ X
--   record { b = a } ≟ x
-- when checking that the pattern c has type D X x

-- SHOULD: succeed

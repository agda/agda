-- Andreas, 2016-12-30, issues #555 and #1886, reported by nad

-- Hidden parameters can be omitted in the repetition
-- of the parameter list.

record R {a} (A : Set a) : Set a

record R A where
  constructor c
  field f : A

testR : ∀{a}{A : Set a}(x : A) → R A
testR x = c x

data D {a} (A : Set a) : Set a

data D A where
  c : A → D A

testD : ∀{a}{A : Set a}(x : A) → D A
testD x = c x

-- Now, c is overloaded, should still work.
testR' : ∀{a}{A : Set a}(x : A) → R A
testR' x = c x

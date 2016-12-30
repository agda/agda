-- Andreas, 2016-12-30, issues #555 and #1886, reported by nad

-- Hidden parameters can be omitted in the repetition
-- of the parameter list.

record R {a} (A : Set a) : Set a

record R A where
  field f : A

data D {a} (A : Set a) : Set a

data D A where
  c : A → D A

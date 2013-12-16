postulate
  A : Set
  a : A

data D : A → Set where
  d : (a : A) → D a

f : D a → Set
f (d a) = A

-- Bad error:
-- a != a of type A
-- when checking that the pattern d a has type D a

-- Better error:
-- a != a of type A
-- (because one is a variable and one a defined identifier)
-- when checking that the pattern d a has type D a

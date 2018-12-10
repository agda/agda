postulate
  A : Set
  a : A

data D : A → Set where
  d : (a : A) → D a

f : A → (D a → Set) → Set
f a f = f (d a)

-- Bad error:
-- a != a of type A
-- when checking that the pattern d a has type D a

-- Better error:
-- a != a of type A
-- (because one is a variable and one a defined identifier)
-- when checking that the pattern d a has type D a

-- Jesper, 2018-12-10: New error (even better?):
-- a != Issue998.a of type A
-- when checking that the expression d a has type D Issue998.a

postulate
  A : Set

data D : Set → Set₁ where
  d : (A : Set) → D A

f : Set → (D A → Set) → Set
f A f = f (d A)

-- Expected error:
-- A != A of type Set
-- (because one is a variable and one a defined identifier)
-- when checking that the pattern d A has type D A

-- Jesper, 2018-12-10: New error:
-- A != Issue998a.A of type Set
-- when checking that the expression d A has type D Issue998a.A

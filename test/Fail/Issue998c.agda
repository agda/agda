postulate
  A : Set

f : (B : Set) → B → A
f A a = a

-- Expected error:
-- A !=< A of type Set
-- (because one is a variable and one a defined identifier)
-- when checking that the expression a has type A

-- Jesper, 2018-12-10: New error:
-- A != Issue998a.A of type Set
-- when checking that the expression d A has type D Issue998a.A

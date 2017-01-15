-- Andreas, 2016-12-20, issue #2348, testing nameFirstIfHidden

-- {-# OPTIONS -v tc.proj.like:100 #-}

{-# OPTIONS --show-implicit #-} -- NEEDED

-- something projection-like

record Wrap (A : Set) : Set where
  field out : A

proj-like : {A : Set} {{r : Wrap A}} → A
proj-like {{r}} = Wrap.out r

-- display term with projection-like thing

postulate
  B : Set
  b : B
  P : B → Set
  p : P b
  instance
    w : Wrap B

ok = P (proj-like {{w}})  -- instance argument does not have to be named

test : P (proj-like)
test = p  -- triggers error message

-- Expected error:
-- b != Wrap.out w of type B
-- when checking that the expression p has type P (proj-like _ {{w}})

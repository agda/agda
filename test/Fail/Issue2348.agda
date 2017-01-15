-- Andreas, 2016-12-20, issue #2348

-- {-# OPTIONS -v tc.proj.like:100 #-}

{-# OPTIONS --show-implicit #-} -- NEEDED

-- something projection like

record Wrap (A : Set) : Set where
  field out : A

proj-like : {{A : Set}} {{r : Wrap A}} → A
proj-like {{r = r}} = Wrap.out r

-- display term with projection like thing

postulate
  B : Set
  b : B
  P : B → Set
  p : P b
  instance
    w : Wrap B

ok = proj-like {{B}} {{r = w}}

test : P (proj-like {{B}})
test = p  -- triggers error message

-- EXPECTED ERROR:
-- b != Wrap.out w of type B
-- when checking that the expression p has type P (proj-like {{r = w}})

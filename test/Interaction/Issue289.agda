module Issue289 where

data D : Set where
  d : D

record ⊤ : Set where

foo : (x y : D) → ⊤
foo d y = {!y!}

-- WAS:
-- Right hand side must be a single hole when making a case
-- distinction.
-- when checking that the expression ? has type ⊤

-- THEN: (Andreas, 2013-03-22)
-- Since goal is solved, further case distinction is not supported;
-- try `Solve constraints' instead
-- when checking that the expression ? has type ⊤

-- NOW: (Andreas, 2016-06-08)
-- Case splitting works!

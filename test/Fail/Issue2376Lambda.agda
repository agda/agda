-- Andreas, 2017-01-05, issue #2376
-- Ensure correct printing for termination error

-- {-# OPTIONS -v term.clause:30 #-}

postulate
  id : ∀{a}{A : Set a} → A → A
  A : Set
  P : A → Set

f : {a : A} → P a → {b : A} → P b → Set
f = λ p → f (id p)  -- id to prevent eta-contration before termination checking

-- Expected termination error:
-- ...
-- Problematic calls:
--   f (id p)

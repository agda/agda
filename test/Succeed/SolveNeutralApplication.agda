
-- This example comes from the discussion on Issue423.
module SolveNeutralApplication where

postulate
  A : Set
  a b : A
  T : A → Set
  mkT : ∀ a → T a
  phantom : A → A → A

data Bool : Set where
  true false : Bool

f : Bool → A → A
f true  x = phantom x a
f false x = phantom x b
-- Andreas, 2012-09-07: the original f did not have "phantom x",
-- thus, x was cleary unused.  With fixing issue 691 Agda tracks
-- constant functions in the type system, thus, reasoning as below
-- no longer works.  We have to make f use its second argument.

-- We can solve the constraint
--   f x _4 == f x y
-- with
--   _4 := y
-- since the application of f is neutral.
g : (x : Bool)(y : A) → T (f x y)
g x y = mkT (f x _)


-- This example comes from the discussion on Issue423.
module SolveNeutralApplication where

postulate
  A : Set
  a b : A
  T : A → Set
  mkT : ∀ a → T a

data Bool : Set where
  true false : Bool

f : Bool → A → A
f true x = a
f false x = b

-- We can solve the constraint
--   f x _4 == f x y
-- with
--   _4 := y
-- since the application of f is neutral.
g : (x : Bool)(y : A) → T (f x y)
g x y = mkT (f x _)

-- Andreas, 2012-03-09 do not solve relevant meta variable by irr. constraint
module Issue351a where

open import Common.Irrelevance
open import Common.Equality

data Bool : Set where
  true false : Bool

-- the Boolean b is not(!) constrained by the equation
f : (b : Bool) -> squash b ≡ squash true -> Bool
f b _ = b

test = f _ refl
-- meta needs to remain unsolved

-- Andreas, 2019-12-03, issue #4200 reported and testcase by nad

open import Agda.Builtin.Bool

data D : Set where
  c₁ : D
  @0 c₂ : D  -- Not allowed

d : D
d = c₂

f : D → Bool
f c₁ = true
f c₂ = false

-- Expected error:

-- Erased constructors are not supported
-- when checking the constructor c₂ in the declaration of D

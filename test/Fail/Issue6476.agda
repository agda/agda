-- Andreas, 2023-01-26, issue #6476 reported by @nad
-- Do not crash on ill-typed display forms.

open import Agda.Builtin.Nat
open import Agda.Builtin.Equality

record R : Set where
  constructor c
  field
    m n : Nat

{-# DISPLAY c m = m #-}

r : R
r = c zero zero

test : c 0 0 ≡ c 1 1
test = refl

-- Expected error:

-- 0 != 1 of type Nat
-- when checking that the expression refl has type 0 0 ≡ 1 1

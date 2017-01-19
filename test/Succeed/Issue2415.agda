-- Andreas, 2017-01-19, issue #2415
-- Bug in size solver (bug in substitution of solution into size expressions)

-- {-# OPTIONS -v tc.size.solve:40 #-}

open import Common.Size
open import Common.Equality

data Nat i : Set where
  zero : Nat i
  suc  : (j : Size< i) (n : Nat j) → Nat i

postulate
  divideBySuc : Nat ∞ → ∀ k → Nat k → Nat k
  div-self : ∀ l (n : Nat l) → divideBySuc n _ (suc l n) ≡ suc _ zero

-- WAS:
-- Cannot solve size constraints
-- [i, n] i ≤ _j_19 i n
-- [i, n] (↑ _j_19 i n) ≤ _i_18 i n
-- [i, n] (↑ _j_20 i n) ≤ _i_18 i n
-- Reason: inconsistent upper bound for 20
-- when checking that zero is a valid argument to a function of type

-- Should succeed.

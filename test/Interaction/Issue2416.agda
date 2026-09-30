-- Andreas, 2017-01-19, issue #2416, probably regression
-- Give failed for constrained size

-- {-# OPTIONS -v interaction.give:40 #-}
-- {-# OPTIONS -v tc.conv:10 #-}
-- {-# OPTIONS -v tc.conv.coerce:70 #-}
-- {-# OPTIONS -v tc.size:40 #-}
-- {-# OPTIONS -v tc.check.internal:40 #-}

{-# OPTIONS --sized-types #-}

open import Common.Size
open import Common.Equality

data Nat i : Set where
  zero : Nat i
  suc  : (j : Size< i) (n : Nat j) → Nat i

postulate
  divideBySuc : Nat ∞ → ∀ k → Nat k → Nat k
  div-self : ∀ l (n : Nat l) → divideBySuc n (↑ l) (suc {! l !} n) ≡ suc l zero

-- Cannot solve size constraints
-- [i, n] i ≤ _j_19 i n
-- [i, n] (↑ _j_19 i n) ≤ _i_18 i n
-- [i, n] (↑ _j_20 i n) ≤ _i_18 i n
-- Reason: inconsistent upper bound for 20
-- when checking that zero is a valid argument to a function of type

-- Andreas, 2019-02-23, re #3578, less reduction in the unifier.
-- Non-interactive version of interaction/Issue635c.agda.

-- {-# OPTIONS -v tc.lhs.unify:50 #-}

open import Common.Bool
open import Common.Equality
open import Common.Product

test : (p : Bool × Bool) → proj₁ p ≡ true → Set
test _ refl = Bool

-- Tests that the unifier does the necessary weak head reduction.

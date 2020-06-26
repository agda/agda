-- Andreas, 2020-06-24, issue #4775 reported by JakobBruenker
-- Non-record patterns in lets and lambdas lead to internal error

-- {-# OPTIONS -v tc.term.lambda:30 #-}
-- {-# OPTIONS -v tc.lhs:15 #-}
-- {-# OPTIONS -v tc.term.let.pattern:30 #-}
-- -- {-# OPTIONS -v tc.term.let.pattern:80 #-}

open import Agda.Builtin.Nat
open import Agda.Builtin.Sigma

data IsSuc : Nat → Set where
  isSuc : ∀ y → IsSuc (suc y)

test : Σ Nat IsSuc → Set
test = λ (y1 , isSuc y2) → Nat

-- ERROR NOW:
-- Expected record pattern
-- when checking the let binding y1 , isSuc y2 = .patternInTele0

-- (Talks about desugaring; could still be improved.)

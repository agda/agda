-- Andreas, 2016-06-16 Issue #2045
-- Size solver should be called before checking extended lambda

-- {-# OPTIONS -v tc.term.exlam:100 #-}

{-# OPTIONS --sized-types #-}

open import Common.Size

postulate anything : ∀{a}{A : Set a} → A

data Exp : Size → Set where
  abs : ∀ i (t : Exp i) → Exp (↑ i)

data Val : ∀ i (t : Exp i) → Set where
  valAbs : ∀ i (t : Exp i) → Val (↑ i) (abs i t)

data Whnf i (t : Exp i) : Set where
  immed : (v : Val i t) → Whnf i t

postulate
  Evaluate : ∀ i (t : Exp i) (P : (w : Whnf i t) → Set) → Set

worksE : ∀ i (fa : Exp i) → Set
worksE i fa = Evaluate i fa λ{ (immed (valAbs _ _)) → anything }

works : ∀ i (fa : Exp i) → Set
works i fa = Evaluate i fa aux
  where
  aux : Whnf i fa → Set
  aux (immed (valAbs _ _)) = anything

test : ∀ i (fa : Exp i) → Set
test i fa = Evaluate _ fa λ{ (immed (valAbs _ _)) → anything }

-- Should work.

-- WAS:
-- extended lambda's implementation ".extendedlambda1" has type:
-- (Whnf (_38 i fa) fa → Set)

-- Cannot instantiate the metavariable _38 to solution (↑ i₁) since it
-- contains the variable i₁ which is not in scope of the metavariable
-- or irrelevant in the metavariable but relevant in the solution
-- when checking that the pattern (valAbs _ _) has type
-- (Val (_38 i fa) fa)

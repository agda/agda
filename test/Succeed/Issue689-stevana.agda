-- Andreas, 2017-10-04, issue #689, test case by stevana
{-# OPTIONS --large-indices #-}
-- {-# OPTIONS -v tc.data:50 #-}
-- {-# OPTIONS -v tc.force:100 #-}
-- {-# OPTIONS -v tc.constr:50 #-}
-- {-# OPTIONS -v tc.conv.sort:30 #-}
-- {-# OPTIONS -v tc.conv.nat:30 #-}

open import Agda.Primitive

data L {a} (A : Set a) : Set a where
  _∷_ : A → L A → L A

data S {a} {A : Set a} : L A → Set₁ where
  _∷_ : (x : A) → (xs : L A) → S (x ∷ xs)  -- x and xs are forced!

-- Should succeed without unsolved constraints.

-- There was a problem in the forcing analysis which I introduced
-- with apparently improper use of `noConstraints` (still do not know why)
-- for the Big/Small Forced argument analysis.
-- The latter one is obsolete and thus removed.

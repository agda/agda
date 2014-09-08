-- Andreas, 2013-03-20
-- Without termination checking disabled, the positivity checker
-- will throw an error.
module NoTerminationCheckPositivity where

open import Common.Level

module M {a}{A : Set a}(K : A → A → A) where

  {-# NON_TERMINATING #-}
  -- F fails the termination check
  F : A → A
  F X = K X (F X)

K : Set → Set → Set
K X Y = X

open M K

data E : Set where
  e : F E → E

-- Since F is non-terminating and hence excluded from unfolding
-- in the positivity checker, it will complain unless termination
-- checking is off.

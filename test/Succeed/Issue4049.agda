-- Andreas, 2019-10-21, issue #4049
-- reported and test case by andy-morris

open import Agda.Builtin.Size

data A : Size → Set
B = A

data A where
  a : ∀ i → B i

-- WAS (2.6.0): internal error in Polarity.hs

-- Should succeed.

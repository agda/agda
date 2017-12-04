-- Andreas, 2017-12-04, issue #2862, reported by m0davis, case for records
-- Regression in development version 2.5.4

-- Scope checker allowed definition in different module than signature

module _ where

module N where
  record R : Set where

open N hiding (module R)

module M where
  record R where  -- should be rejected since signature lives in different module

  inhabited-R : R
  inhabited-R = _

data ⊥ : Set where

record R where
  field absurd : ⊥

boom : ⊥
boom = R.absurd M.inhabited-R

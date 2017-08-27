-- Andreas, 2017-08-18, issue #2703, reported by davdar, testcase by gallais
-- Underapplied constructor triggers internal error

{-# OPTIONS --allow-unsolved-metas #-}

-- {-# OPTIONS -v tc.getConType:35 #-}

postulate
  A : Set

data Sg : A → Set where
  sg : ∀ t → Sg t  -- Target type depends on constructor argument

postulate
  cut : (∀ t → Sg t) → Set

bug : cut sg  -- Underapplied constructor
bug with A
bug | _ = _

-- Was: internal error in 2.5.3 RC1

-- Should succeed with unsolved meta.

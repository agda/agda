-- Andreas, 2017-11-06, issue #2840 reported by wenkokke

Id : (F : Set → Set) → Set → Set
Id F = F

data D (A : Set) : Set where
  c : Id _ A

-- WAS: internal error in positivity checker

-- EXPECTED: success, or
-- The target of a constructor must be the datatype applied to its
-- parameters, _F_2 A isn't
-- when checking the constructor c in the declaration of D

-- Andreas, 2011-04-14
-- {-# OPTIONS -v tc.cover:20 -v tc.lhs.unify:20 #-}
{-# OPTIONS --guardedness #-}

module Issue291b where

open import Common.Coinduction
open import Common.Equality

data RUnit : Set where
  runit : ∞ RUnit -> RUnit

j : (u : RUnit) -> u ≡ runit (♯ u) -> Set
j u ()

-- needs to fail because of a non strongly rigid occurrence
-- ♯ does not count as a constructor, and that is good!

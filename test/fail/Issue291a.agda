-- Andreas, 2011-04-14
-- {-# OPTIONS -v tc.cover:20 -v tc.lhs.unify:20 #-}
module Issue291a where

open import Imports.Coinduction

data _≡_ {A : Set}(a : A) : A -> Set where
  refl : a ≡ a

data RUnit : Set where
  runit : ∞ RUnit -> RUnit

j : (u : ∞ RUnit) -> ♭ u ≡ runit u -> Set
j u ()
-- needs to fail (reports a Bad split!)

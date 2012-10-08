-- Andreas, 2012-09-07
-- {-# OPTIONS -v tc.polarity:10 -v tc.conv.irr:20 -v tc.conv.elim:25 -v tc.conv.term:10 #-}
module Issue691 where

open import Common.Equality

data Bool : Set where
  true false : Bool

assert : (A : Set) → A → Bool → Bool
assert _ _ true  = true
assert _ _ false = false

g : Bool -> Bool -> Bool
g x true  = true
g x false = true

unsolved : Bool -> Bool
unsolved y =
  let X : Bool
      X = _
  in  assert (g X y ≡ g true y) refl X
-- X should be left unsolved

istrue : (unsolved false) ≡ true
istrue = refl



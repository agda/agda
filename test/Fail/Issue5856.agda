-- Andreas, 2022-03-28, issue #5856, reported by Szumi Xie.
-- Patterns in path-lambdas were simply ignored, but should be illegal.

{-# OPTIONS --cubical #-}

-- {-# OPTIONS -v tc.term.lambda:30 #-}

open import Agda.Builtin.Cubical.Path

postulate
  A E : Set
  a : A

data C : Set where
  c : E → C

p : a ≡ a
p = λ (c e) → a

-- WAS: accepted.

-- Expected error:
-- Patterns are not allowed in Path-lambdas
-- when checking that the expression λ .patternInTele0 @ (c e) → a has type a ≡ a

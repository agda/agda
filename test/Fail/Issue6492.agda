-- Andreas, 2026-05-01, issue #6492, shrunk test case by Amelia.
-- Debug printing crashed because of wrong context.

{-# OPTIONS -v tc.meta.eta:15 #-}

open import Agda.Builtin.Sigma
open import Agda.Builtin.Bool
open import Agda.Builtin.Unit

data T : Bool → Set where
  true : T true

f : (x : Σ Bool λ _ → Bool) → T (x .fst) → ⊤
f _ _ = tt

foo : Bool → ⊤
foo _ = f _ true

-- WAS: debug printing crashed.

-- Expected error: UnsolvedMetaVariables

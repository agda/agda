-- Andreas, 2026-10-05
-- Issue #8808: internal error during cubical boundary recovery.
-- Reported and testcase by @tomjack.
-- Unbound de Bruijn index when recovering the boundary of an interaction point
-- through a meta that instantiates to a lambda.

{-# OPTIONS --cubical #-}

open import Agda.Primitive renaming (Set to Type)
open import Agda.Primitive.Cubical renaming (primTransp to transp)
open import Agda.Builtin.Cubical.Path

refl : {A : Type} {x : A} → x ≡ x
refl {x = x} = λ _ → x

Ω Ω² : (A : Type) → A → Type
Ω A x = x ≡ x
Ω² A x = Ω (Ω A x) refl

postulate
  S² : Type
  base : S²

test : transp (λ _ → Ω² S² base) i0 refl ≡ refl
test = λ i a b → {!!}

-- WAS: internal error in lookupBV

-- Expected:
-- ?0 : S²
-- ———— Error —————————————————————————————————————————————————
-- error: [UnsolvedConstraints]
-- Unsolved constraints
-- ———— Warnings ——————————————————————————————————————————————
-- warning: -W[no]InteractionMetaBoundaries
-- Interaction meta(s) at the following location(s) have unsolved
-- boundary constraints:
--   ...

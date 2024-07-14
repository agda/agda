-- See #7277
{-# OPTIONS --type-based-termination #-}
{-# OPTIONS --sized-types #-}

module TypeBasedTermination.RecursionInPiType where

open import Agda.Builtin.Size
open import Agda.Builtin.Equality

-- The following should not termination check,
-- otherwise eta expansion can loop
T : Size → Set
T i = (j : Size< i) → T j

-- This loops:
loops : (i : Size) (x y : T i) → x ≡ y
loops i x y = refl

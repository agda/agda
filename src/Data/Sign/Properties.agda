------------------------------------------------------------------------
-- Some properties about signs
------------------------------------------------------------------------

module Data.Sign.Properties where

open import Data.Empty
open import Data.Function
open import Data.Sign
open import Relation.Binary.PropositionalEquality

-- The opposite of a sign is not equal to the sign.

opposite-not-equal : ∀ s → s ≢ opposite s
opposite-not-equal - ()
opposite-not-equal + ()

-- Sign multiplication is right cancellative.

cancel-*-right : ∀ s₁ s₂ {s} → s₁ * s ≡ s₂ * s → s₁ ≡ s₂
cancel-*-right - - _  = refl
cancel-*-right - + eq = ⊥-elim (opposite-not-equal _ $ sym eq)
cancel-*-right + - eq = ⊥-elim (opposite-not-equal _ eq)
cancel-*-right + + _  = refl

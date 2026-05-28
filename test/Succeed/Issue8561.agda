-- Andreas, 2026-05-11, issue #8561 already fixed at 2.8.0
-- The master of the standard-library does not build with Agda 2.7
-- Reported by Vekhir, shrunk by shhyou and friendly NHI

open import Agda.Primitive using (Level; lsuc; _⊔_)

record Setoid (c : Level) : Set (lsuc c) where
  field
    Carrier : Set c

record StrictTotalOrder (c ℓ₁ ℓ₂ : Level) : Set (lsuc (c ⊔ ℓ₁ ⊔ ℓ₂)) where
  field
    Carrier : Set c

  module Eq where
    setoid : Setoid c
    setoid = record
      { Carrier = Carrier
      }

module ValueMod {a} (S : Setoid a) where

  open Setoid S renaming (Carrier to Key)

  record Value (v : Level) : Set (a ⊔ lsuc v) where
    field
      family : Key → Set v

module _ {a ℓ₁ ℓ₂} (strictTotalOrder : StrictTotalOrder a ℓ₁ ℓ₂) where

  open StrictTotalOrder strictTotalOrder
    using (module Eq) renaming (Carrier to Key)

  open ValueMod Eq.setoid public

  private
    variable
      v : Level

  module _ {V : Value v}
    (open Value V renaming (family to Val))
    where

    postulate
      foo : ∀ k → Val k

-- Error WAS (Agda <= 2.7.0.1):
-- src/full/Agda/TypeChecking/Reduce/Fast.hs:937:19-53: Non-exhaustive patterns in Just n

-- Should succeed.

{-# OPTIONS --erased-cubical --erasure #-}

open import Agda.Builtin.Cubical.Glue
open import Agda.Primitive
open import Agda.Primitive.Cubical

-- Glue must only be used in erased contexts when --erased-cubical is
-- active.

_ : SSet (lsuc lzero)
_ =
  (φ : I) (A : Set) (B : Partial φ Set)
  (f : PartialP φ (λ x → B x ≃ A)) →
  primGlue A B f

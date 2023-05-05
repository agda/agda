{-# OPTIONS --erasure #-}

module _ where

open import Agda.Builtin.Nat
open import Agda.Builtin.Equality

postulate
  String : Set
{-# BUILTIN STRING String #-}

primitive
  @0 ⦃ primShowNat ⦄ : Nat → String

-- Wrong modality for primitive primShowNat
--   Got:      instance, erased
--   Expected: visible, unrestricted
-- when checking that the type of the primitive function primShowNat
-- is Nat → String

{-# OPTIONS --erasure #-}

module _ where

open import Agda.Builtin.Nat
open import Agda.Builtin.Equality

postulate
  String : Set
{-# BUILTIN STRING String #-}

primitive
  @0 primShowNat : Nat → String

-- error: [WrongArgInfoForPrimitive]
-- Wrong definition properties for primitive primShowNat
--   Got:      at modality erased
--   Expected: at modality default

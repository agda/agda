
module Common.TC where

open import Common.Reflection
open import Common.Prelude

postulate
  TC       : ∀ {a} → Set a → Set a
  returnTC : ∀ {a} {A : Set a} → A → TC A
  bindTC   : ∀ {a b} {A : Set a} {B : Set b} → TC A → (A → TC B) → TC B
  unifyTC  : Term → Term → TC ⊤

{-# BUILTIN AGDATCM       TC #-}
{-# BUILTIN AGDATCMRETURN returnTC #-}
{-# BUILTIN AGDATCMBIND   bindTC #-}
{-# BUILTIN AGDATCMUNIFY  unifyTC #-}

{-# OPTIONS --without-K --safe --no-universe-polymorphism --no-sized-types --no-guardedness #-}

module Agda.Builtin.Word where

open import Agda.Builtin.Nat

{-# BUILTIN WORD64 Word64 #-}

primitive
  primWord64ToNat   : Word64 → Nat
  primWord64FromNat : Nat → Word64

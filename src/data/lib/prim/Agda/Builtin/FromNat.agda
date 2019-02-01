{-# OPTIONS --without-K --safe --no-sized-types --no-guardedness #-}

module Agda.Builtin.FromNat where

open import Agda.Primitive
open import Agda.Builtin.Nat

record Number {a} (A : Set a) : Set (lsuc a) where
  field
    Constraint : Nat → Set a
    fromNat : ∀ n → {{_ : Constraint n}} → A

open Number {{...}} public using (fromNat)

{-# BUILTIN FROMNAT fromNat #-}
{-# DISPLAY Number.fromNat _ n = fromNat n #-}

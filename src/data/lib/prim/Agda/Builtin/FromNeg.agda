{-# OPTIONS --without-K --safe --no-sized-types --no-guardedness #-}

module Agda.Builtin.FromNeg where

open import Agda.Primitive
open import Agda.Builtin.Nat

record Negative {a} (A : Set a) : Set (lsuc a) where
  field
    Constraint : Nat → Set a
    fromNeg : ∀ n → {{_ : Constraint n}} → A

open Negative {{...}} public using (fromNeg)

{-# BUILTIN FROMNEG fromNeg #-}
{-# DISPLAY Negative.fromNeg _ n = fromNeg n #-}

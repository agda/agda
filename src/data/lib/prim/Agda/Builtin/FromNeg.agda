{-# OPTIONS --cubical-compatible --safe --no-sized-types
            --no-guardedness --level-universe --erasure #-}

module Agda.Builtin.FromNeg where

open import Agda.Primitive
open import Agda.Builtin.Nat

record Negative {@0 a} (A : Set a) : Set (lsuc a) where
  field
    Constraint : Nat → Set a
    fromNeg : ∀ n → {{_ : Constraint n}} → A

open Negative {{...}} public using (fromNeg)

{-# BUILTIN FROMNEG fromNeg #-}
{-# DISPLAY Negative.fromNeg _ n = fromNeg n #-}

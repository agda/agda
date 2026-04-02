{-# OPTIONS --cubical-compatible --safe --no-sized-types
            --no-guardedness --level-universe --erasure #-}

module Agda.Builtin.Strict where

open import Agda.Builtin.Equality

primitive
  primForce      : ∀ {@0 a b} {A : Set a} {B : A → Set b} (x : A) → (∀ x → B x) → B x
  primForceLemma : ∀ {@0 a b} {A : Set a} {B : A → Set b} (x : A) (f : ∀ x → B x) → primForce x f ≡ f x

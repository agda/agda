-- Tests handling of projection-like functions
{-# OPTIONS --type-based-termination --no-syntax-based-termination #-}

module TypeBasedTermination.ProjectionLike where

data Nat : Set where
  zero : Nat
  suc  : Nat → Nat

record Foo (A : Set) : Set where
  field
    id : A → A

record Wrp (A : Set) : Set where
  field
    foo : Foo A

  open Foo foo public


record Wrp2 (A : Set) : Set where
  field
    wrp : Wrp A

  open Wrp wrp public


wrpp : ∀ A → Wrp2 A
wrpp A = record
  { wrp = record
    { foo = record
      { id = λ x → x
      }
    }
  }

private
  open module RR = Wrp2 (wrpp Nat)

module Prop where
  d : Nat → Nat
  d zero = zero
  d (suc n) = (d (id n))

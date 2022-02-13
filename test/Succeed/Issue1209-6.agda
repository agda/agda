-- By default both sized types and constructor-based guardedness are
-- available.
-- Jesper, 2021-05-12: This is no longer the case, you now have to
-- ask for the combination explicitly.

{-# OPTIONS --guardedness --sized-types #-}

open import Agda.Builtin.Size

record Stream (A : Set) : Set where
  coinductive
  field
    head : A
    tail : Stream A

open Stream

repeat : ∀ {A} → A → Stream A
repeat x .head = x
repeat x .tail = repeat x

record Sized-stream (A : Set) (i : Size) : Set where
  coinductive
  field
    head : A
    tail : {j : Size< i} → Sized-stream A j

open Sized-stream

postulate
  destroy-guardedness : {A : Set} → A → A

repeat-sized : ∀ {A i} → A → Sized-stream A i
repeat-sized x .head = x
repeat-sized x .tail = destroy-guardedness (repeat-sized x)

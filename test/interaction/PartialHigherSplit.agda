{-# OPTIONS --cubical --safe #-}
module PartialHigherSplit where

open import Agda.Primitive
open import Agda.Builtin.Nat
open import Agda.Primitive.Cubical
open import Agda.Builtin.Cubical.Path

data ℤ : Set where
  pos : (n : Nat) → ℤ
  neg : (n : Nat) → ℤ
  posneg : pos 0 ≡ neg 0

-- copied and adapted from Cubical.Data.Int.MoreInts.QuoInt.Base

sucℤ : ℤ → ℤ
sucℤ (pos n)       = pos (suc n)
sucℤ (neg zero)    = pos 1
sucℤ (neg (suc n)) = neg n
sucℤ (posneg _)    = pos 1

predℤ : ℤ → ℤ
predℤ (neg n)       = neg (suc n)
predℤ (pos zero)    = neg 1
predℤ (pos (suc n)) = pos n
predℤ (posneg _)    = neg 1

_+ℤ_ : ℤ → ℤ → ℤ
m +ℤ (pos (suc n)) = sucℤ   (m +ℤ pos n)
m +ℤ (neg (suc n)) = predℤ  (m +ℤ neg n)
m +ℤ _             = m

0+ : ∀ a → pos zero +ℤ a ≡ a
0+ (pos (suc n)) = {!   !}
0+ (neg (suc n)) = {!   !}
0+ a = {! a !}

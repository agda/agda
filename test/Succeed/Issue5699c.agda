{-# OPTIONS --allow-unsolved-metas #-}

open import Agda.Builtin.List
open import Agda.Builtin.Nat
open import Agda.Builtin.Unit
open import Agda.Builtin.Bool
open import Agda.Builtin.Reflection renaming (bindTC to _>>=_)

data D (A : Set) : Set where
  c : A → D A

f : (A : Set) → D A → A
f A (c x) = x

macro
  m : Term → TC ⊤
  m hole = withReconstructed true do
    qf ← quoteTC (f Nat (c 0))
    uqf ← unquoteTC {A = Nat} qf
    returnTC _

test = m

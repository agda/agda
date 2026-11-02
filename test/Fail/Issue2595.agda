-- Andreas, 2026-10-30, issue #2595, reported 2017-05-29 by Andreas.
-- Shape-irrelevance broke constraint solving:
-- the meta for nada : IsTrue false was solved by tt : IsTrue true.

{-# OPTIONS --experimental-irrelevance #-}

open import Agda.Builtin.Equality

data ⊥ : Set where

data Bool : Set where
  true false : Bool

data IsTrue : ..(x : Bool) → Set where
  tt : IsTrue true

mutual

  nada : IsTrue false
  nada = _

  -- Comparing H true tt with H false nada skips the irrelevant argument
  -- and then compares tt : IsTrue true with nada : IsTrue false.
  -- The solution nada := tt has to be rejected.

  solve : {H : ∀ .x (z : IsTrue x) → Set} → H true tt ≡ H false nada
  solve = refl

absurd : ⊥
absurd with nada
absurd | ()

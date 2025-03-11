-- Szumi, 2025-03-11, dot-pattern termination is re-enabled for Cubical Agda
-- Test case by Andreas adapted from the test case of #4606 by Andrew Pitts

{-# OPTIONS --cubical #-}

open import Agda.Builtin.Nat using (Nat; zero; suc)

data Acc {A : Set} (R : A → A → Set) (x : A) : Set where
  acc : (∀ y → R y x → Acc R y) → Acc R x

data _<_ (x : Nat) : Nat → Set where
  <S : x < suc x

iswf< : ∀ x → Acc _<_ x
iswf< x = acc (h x)
  where
  h : ∀ x y → y < x → Acc _<_ y
  h .(suc y) y <S = acc (h y)

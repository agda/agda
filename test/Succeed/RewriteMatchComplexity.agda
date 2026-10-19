{-# OPTIONS --rewriting #-}

module RewriteMatchComplexity where

{-
Checking the asymptotic speedup in PR 8222.
This file should check quickly in linear time
in the size of "n" below.
-}

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ
{-# BUILTIN NATURAL ℕ #-}

data Nat : Set where
  zero : Nat
  suc  : Nat → Nat

ℕ2Nat : ℕ → Nat → Nat
ℕ2Nat zero acc = acc
ℕ2Nat (suc n) acc = ℕ2Nat n (suc acc)

n : Nat
n = ℕ2Nat 30000 zero

postulate
  Id   : {A : Set} → A → A → Set
  refl : ∀ {A} n → Id {A} n n

  f     : Nat → Nat
  fsuc  : ∀ n → Id (f (suc n)) (f n)
  fzero : Id (f zero) zero
{-# BUILTIN REWRITE Id #-}
{-# REWRITE fsuc fzero #-}

test : Id (f n) zero
test = refl zero

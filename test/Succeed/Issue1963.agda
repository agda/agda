-- Andreas, May - July 2016, implementing postfix projections

{-# OPTIONS --guardedness #-}

module Issue1963 where

module Prod where

  record Σ (A : Set) (B : A → Set) : Set where
    field fst : A
          snd : B fst

  open Σ

  test : ∀{A} → A → Σ A λ _ → A
  test = λ where
    x .fst → x
    x .snd → x

module Stream where

  record Stream (A : Set) : Set where
    coinductive
    pattern  -- 2020-04-19, issue #4560, ignored for coinductive records.
    field head : A
          tail : Stream A

  open Stream

  repeat : ∀{A} (a : A) → Stream A
  repeat a .head = a
  repeat a. tail = repeat a

  zipWith : ∀{A B C} (f : A → B → C) (s : Stream A) (t : Stream B) → Stream C
  zipWith f s t .head = f (s .head) (t .head)
  zipWith f s t .tail = zipWith f (s .tail) (t .tail)

  module Fib (Nat : Set) (zero one : Nat) (plus : Nat → Nat → Nat) where

    {-# TERMINATING #-}
    fib : Stream Nat
    fib .head = zero
    fib .tail .head = one
    fib .tail .tail = zipWith plus fib (fib .tail)

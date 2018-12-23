{-# OPTIONS --guardedness #-}
-- {-# OPTIONS -v term:30 #-}
-- 2010-10-14
module ProjectionsPreserveGuardednessTrivialExample where

open import Common.Level
open import Common.Coinduction
open import Common.Product

-- Streams

infixr 5 _∷_

data Stream (A : Set) : Set where
  _∷_ : (x : A) (xs : ∞ (Stream A)) → Stream A

mutual

  repeat : {A : Set}(a : A) → Stream A
  repeat a = a ∷ proj₂ (repeat' a)

  repeat' : {A : Set}(a : A) → A × ∞ (Stream A)
  repeat' a = a , ♯ repeat a

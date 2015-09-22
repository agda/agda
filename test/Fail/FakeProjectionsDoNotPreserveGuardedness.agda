-- 2010-10-14

-- {-# OPTIONS -v term:20 #-}
module FakeProjectionsDoNotPreserveGuardedness where

import Common.Level
open import Common.Coinduction

-- Products

infixr 4 _,_
infixr 2 _×_

-- fake product with projections
postulate
  _×_   : (A B : Set) → Set
  _,_   : {A B : Set}(a : A)(b : B) → A × B
  proj₁ : {A B : Set}(p : A × B) → A
  proj₂ : {A B : Set}(p : A × B) → B

-- Streams

infixr 5 _∷_

data Stream (A : Set) : Set where
  _∷_ : (x : A) (xs : ∞ (Stream A)) → Stream A

mutual

  repeat : {A : Set}(a : A) → Stream A
  repeat a = a ∷ proj₂ (repeat' a)

  repeat' : {A : Set}(a : A) → A × ∞ (Stream A)
  repeat' a = a , ♯ repeat a

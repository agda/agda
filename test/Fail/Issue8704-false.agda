{-# OPTIONS --safe --without-K #-}

open import Agda.Builtin.Nat
open import Agda.Builtin.Bool
open import Agda.Builtin.Unit
open import Agda.Builtin.Equality

data Empty : Set where

data Vec (A : Set) : Nat → Set where
  []  : Vec A zero
  _∷_ : {n : Nat} → A → Vec A n → Vec A (suc n)

g : (n : Nat) → Vec ⊤ n → Bool → Bool
g n (y ∷ ys) b     = true
g n v        true  = false
g n v        false = false
  module Leak where
    abstract
      hh : Nat
      hh = suc zero
    vv : Vec ⊤ hh
    vv = _
    data Is : Vec ⊤ hh → Set where
      mk : (w : Vec ⊤ hh) → Is w
    abstract
      solve : Is vv
      solve = mk (tt ∷ [])
      lemA : g hh vv true ≡ true
      lemA = refl
    lemC : false ≡ true
    lemC = lemA

discr : false ≡ true → Empty
discr ()

absurd : Empty
absurd = discr (Leak.lemC zero [])

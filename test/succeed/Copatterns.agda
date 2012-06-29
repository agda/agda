{-# OPTIONS --copatterns #-}
module Copatterns where

open import Common.Equality

record _×_ (A B : Set) : Set where
  constructor _,_
  field
    fst : A
    snd : B
open _×_

pair : {A B : Set} → A → B → A × B
fst (pair a b) = a
snd (pair a b) = b

swap : {A B : Set} → A × B → B × A
fst (swap p) = snd p
snd (swap p) = fst p

swap3 : {A B C : Set} → A × (B × C) → C × (B × A)
fst (swap3 t)       = snd (snd t)
fst (snd (swap3 t)) = fst (snd t)
snd (snd (swap3 t)) = fst t

-- should also work if we shuffle the clauses
swap4 : {A B C D : Set} → A × (B × (C × D)) → D × (C × (B × A))
fst (snd (swap4 t))       = fst (snd (snd t))
snd (snd (snd (swap4 t))) = fst t
fst (swap4 t)             = snd (snd (snd t))
fst (snd (snd (swap4 t))) = fst (snd t)

-- State monad example

record State (S A : Set) : Set where
  constructor state
  field
    runState : S → A × S
open State

record Monad (M : Set → Set) : Set1 where
  constructor monad
  field
    return : {A : Set}   → A → M A
    _>>=_  : {A B : Set} → M A → (A → M B) → M B
open Monad {{...}}

stateMonad : {S : Set} → Monad (State S)
runState (return {{stateMonad}} a  ) s  = a , s
runState (_>>=_  {{stateMonad}} m k) s₀ =
  let a , s₁ = runState m s₀
  in  runState (k a) s₁

leftId : {A B S : Set}(a : A)(k : A → State S B) → (return a >>= k) ≡ k a
leftId a k = refl

rightId : {A B S : Set}(m : State S A) → (m >>= return) ≡ m
rightId m = refl

assoc : {A B C S : Set}(m : State S A)(k : A → State S B)(l : B → State S C) →
   ((m >>= k) >>= l) ≡ (m >>= λ a → k a >>= l)
assoc m k l = refl

-- multiple clauses with abstractions

fswap3 : {A B C X : Set} → (X → A) × ((X → B) × C) → (X → C) × (X → (B × A))
fst (fswap3 t) x       = snd (snd t)
fst (snd (fswap3 t) y) = fst (snd t) y
snd (snd (fswap3 t) z) = fst t z


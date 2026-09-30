-- {-# OPTIONS -v impossible:100 -v tc.lhs.imp:100 #-}
-- {-# OPTIONS -v impossible:100 -v tc.cover:20 #-}
-- {-# OPTIONS --copatterns #-} -- Andreas, 2015-08-26 on by default.
module Issue957 where

open import Common.Equality

record _×_ (A B : Set) : Set where
  constructor _,_
  field
    fst : A
    snd : B
open _×_

pair : {A B : Set} → A → B → A × B
fst (pair a b) = ?
snd (pair a b) = ?

swap : {A B : Set} → A × B → B × A
fst (swap p) = ?
snd (swap p) = ?

swap3 : {A B C : Set} → A × (B × C) → C × (B × A)
fst (swap3 t)       = ?
fst (snd (swap3 t)) = ?
snd (snd (swap3 t)) = ?

-- should also work if we shuffle the clauses
swap4 : {A B C D : Set} → A × (B × (C × D)) → D × (C × (B × A))
fst (snd (swap4 t))       = ?
snd (snd (snd (swap4 t))) = ?
fst (swap4 t)             = ?
fst (snd (snd (swap4 t))) = ?

-- multiple clauses with abstractions

fswap3 : {A B C X : Set} → (X → A) × ((X → B) × C) → (X → C) × (X → (B × A))
fst (fswap3 t) x       = ?
fst (snd (fswap3 t) y) = ?
snd (snd (fswap3 t) z) = ?


-- State monad example

-- The State newtype

record State (S A : Set) : Set where
  constructor state
  field
    runState : S → A × S
open State

-- The Monad type class

record Monad (M : Set → Set) : Set1 where
  constructor monad
  field
    return : {A : Set}   → A → M A
    _>>=_  : {A B : Set} → M A → (A → M B) → M B

module InstanceArgument where

  open Monad {{...}}

  -- State is an instance of Monad

  instance
    stateMonad : {S : Set} → Monad (State S)
    runState (return {{stateMonad}} a  ) s  = ?
    runState (_>>=_  {{stateMonad}} m k) s₀ = ?

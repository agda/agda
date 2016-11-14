-- {-# OPTIONS -v impossible:100 -v tc.lhs.imp:100 #-}
-- {-# OPTIONS -v impossible:100 -v tc.cover:20 #-}
-- {-# OPTIONS --copatterns #-} -- Andreas, 2015-08-26 on by default.
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

-- multiple clauses with abstractions

fswap3 : {A B C X : Set} → (X → A) × ((X → B) × C) → (X → C) × (X → (B × A))
fst (fswap3 t) x       = snd (snd t)
fst (snd (fswap3 t) y) = fst (snd t) y
snd (snd (fswap3 t) z) = fst t z


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
    runState (return {{stateMonad}} a  ) s  = a , s
    runState (_>>=_  {{stateMonad}} m k) s₀ =
      let a , s₁ = runState m s₀
      in  runState (k a) s₁

  _~_ : {S A : Set} → State S A → State S A → Set
  m ~ m' = ∀ {s} → runState m s ≡ runState m' s

  leftId : {A B S : Set}(a : A)(k : A → State S B) →
    (return a >>= k) ≡ k a
  leftId a k = refl

  rightId : {A B S : Set}(m : State S A) →
    (m >>= return) ≡ m
  rightId m = refl

  assoc : {A B C S : Set}(m : State S A)(k : A → State S B)(l : B → State S C) →
     ((m >>= k) >>= l) ≡ (m >>= λ a → k a >>= l)
  assoc m k l = refl

module NoInstance where

-- State is an instance of Monad

  stateMonad : {S : Set} → Monad (State S)
  runState (Monad.return stateMonad a  ) s  = a , s
  runState (Monad._>>=_  stateMonad m k) s₀ =
    let a , s₁ = runState m s₀
    in  runState (k a) s₁

  module InstantiatedModule {S : Set} where

    open Monad (stateMonad {S})

    leftId : {A B : Set}(a : A)(k : A → State S B) →
      (return a >>= k) ≡ k a
    leftId a k = refl

    rightId : {A B : Set}(m : State S A) →
      (m >>= return) ≡ m
    rightId m = refl

    assoc : {A B C : Set}(m : State S A)(k : A → State S B)(l : B → State S C) →
      ((m >>= k) >>= l) ≡ (m >>= λ a → (k a >>= l))
    assoc m k l = refl

  module VisibleArgument where

    open Monad

    leftId : {A B S : Set}(a : A)(k : A → State S B) →
      (_>>=_ stateMonad (return stateMonad a) k) ≡ k a
    leftId a k = refl

    rightId : {A B S : Set}(m : State S A) →
      (_>>=_ stateMonad m (return stateMonad)) ≡ m
    rightId m = refl

    assoc : {A B C S : Set}(m : State S A)(k : A → State S B)(l : B → State S C) →
       (_>>=_ stateMonad (_>>=_ stateMonad m k) l) ≡
      (_>>=_ stateMonad m λ a → _>>=_ stateMonad (k a) l)
    assoc m k l = refl


  module HiddenArgument where

    return : ∀ {M}{dict : Monad M}{A : Set} → A → M A
    return {dict = dict} = Monad.return dict

    _>>=_ :  ∀ {M}{dict : Monad M}{A B : Set} → M A → (A → M B) → M B
    _>>=_ {dict = dict} = Monad._>>=_ dict

    leftId : {A B S : Set}(a : A)(k : A → State S B) →
      (_>>=_ {dict = stateMonad} (return {dict = stateMonad} a) k) ≡ k a
    leftId a k = refl

  {- LOTS OF YELLOW:

    leftId : {A B S : Set}(a : A)(k : A → State S B) → (return {dict = stateMonad {S}} a >>= k) ≡ k a
    leftId a k = refl

    rightId : {A B S : Set}(m : State S A) → (m >>= return) ≡ m
    rightId m = refl

    assoc : {A B C S : Set}(m : State S A)(k : A → State S B)(l : B → State S C) →
       ((m >>= k) >>= l) ≡ (m >>= λ a → k a >>= l)
    assoc m k l = refl
  -}

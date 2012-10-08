{-# OPTIONS --show-implicit #-}
-- {-# OPTIONS -v tc.def.fun:10 -v tc.def.where:100 #-}

module PartialityMonad where

open import Common.Level
open import Common.Coinduction

record RawMonad {f} (M : Set f → Set f) : Set (lsuc f) where
  infixl 1 _>>=_

  field
    return : ∀ {A} → A → M A
    _>>=_  : ∀ {A B} → M A → (A → M B) → M B


------------------------------------------------------------------------
-- The partiality monad

data _⊥ {a} (A : Set a) : Set a where
  now   : (x : A) → A ⊥
  later : (x : ∞ (A ⊥)) → A ⊥

-- Fails if hidden pattern {f} is removed
monad : ∀ {f} → RawMonad {f = f} _⊥
-- monad {f} = record
monad = record
  { return = now
  ; _>>=_  = _>>=_
  }
  where
  _>>=_ : ∀ {A B} → A ⊥ → (A → B ⊥) → B ⊥
  now x   >>= f = f x
  later x >>= f = later (♯ (♭ x >>= f))

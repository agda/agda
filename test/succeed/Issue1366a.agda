-- Andreas, 2014-11-25, variant of Issue 1366

{-# OPTIONS --copatterns #-}

open import Common.Prelude using (Nat; zero; suc; Unit; unit)

data Vec (A : Set) : Nat → Set where
   []  : Vec A zero
   _∷_ : ∀ {n} → A → Vec A n → Vec A (suc n)

-- Singleton type

data Sg {A : Set} (x : A) : Set where
  sg : Sg x

-- Generalizing Unit → Nat

record DNat : Set₁ where
  field
    D     : Set
    force : D → Nat
open DNat

nonNil : ∀ {n} → Vec Unit n → Nat
nonNil []       = zero
nonNil (i ∷ is) = suc (force f i) where
  f : DNat
  D     f      = Unit
  force f unit = zero

g : ∀ {n} {v : Vec Unit n} → Sg (nonNil v) → Sg v
g sg = sg

one : Sg (suc zero)
one = sg

test : Sg (unit ∷ [])
test = g one

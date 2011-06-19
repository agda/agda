-- 2010-10-14

{-# OPTIONS --universe-polymorphism #-}

module ProjectionsPreserveGuardednessTrivialExample where

-- Coinduction is only available with universe polymorphism

postulate
  Level : Set
  zero : Level
  suc  : (i : Level) → Level
  _⊔_ : Level → Level → Level

{-# BUILTIN LEVEL     Level #-}
{-# BUILTIN LEVELZERO zero  #-}
{-# BUILTIN LEVELSUC  suc   #-}
{-# BUILTIN LEVELMAX _⊔_ #-}

infixl 6 _⊔_

-- Coinduction

infix 1000 ♯_

postulate
  ∞  : ∀ {a} (A : Set a) → Set a
  ♯_ : ∀ {a} {A : Set a} → A → ∞ A
  ♭  : ∀ {a} {A : Set a} → ∞ A → A

{-# BUILTIN INFINITY ∞  #-}
{-# BUILTIN SHARP    ♯_ #-}
{-# BUILTIN FLAT     ♭  #-}

-- Products

infixr 4 _,_ 
infixr 2 _×_ 

record Σ {a b} (A : Set a) (B : A → Set b) : Set (a ⊔ b) where
  constructor _,_
  field
    proj₁ : A
    proj₂ : B proj₁

open Σ public

syntax Σ A (λ x → B) = Σ[ x ∶ A ] B

_×_ : ∀ {a b} (A : Set a) (B : Set b) → Set (a ⊔ b)
A × B = Σ[ x ∶ A ] B

-- Streams

infixr 5 _∷_

data Stream (A : Set) : Set where
  _∷_ : (x : A) (xs : ∞ (Stream A)) → Stream A

mutual

  repeat : {A : Set}(a : A) → Stream A
  repeat a = a ∷ proj₂ (repeat' a)

  repeat' : {A : Set}(a : A) → A × ∞ (Stream A)
  repeat' a = a , ♯ repeat a

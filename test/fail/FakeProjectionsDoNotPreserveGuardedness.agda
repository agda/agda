-- 2010-10-14

{-# OPTIONS --universe-polymorphism #-}

module FakeProjectionsDoNotPreserveGuardedness where

-- Coinduction is only available with universe polymorphism

postulate
  Level : Set
  zero : Level
  suc  : (i : Level) → Level
  _⊔_ : Level → Level → Level

{-# BUILTIN LEVEL     Level #-}
{-# BUILTIN LEVELZERO zero  #-}
{-# BUILTIN LEVELSUC  suc   #-}
{-# BUILTIN LEVELMAX  _⊔_   #-}

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

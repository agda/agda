-- {-# OPTIONS -v tc.lhs.unify.flexflex:100 -v tc.lhs.unify.assign:100 -v tc.lhs:100 #-}
module Multisplit where

postulate
  Level : Set
  lzero : Level
  lsuc  : Level → Level
  _⊔_   : Level → Level → Level

{-# BUILTIN LEVEL     Level #-}
{-# BUILTIN LEVELZERO lzero #-}
{-# BUILTIN LEVELSUC  lsuc  #-}
{-# BUILTIN LEVELMAX  _⊔_   #-}

data Bool : Set where
  true false : Bool

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

data Fin : ℕ → Set where
  zero : ∀ {n} → Fin (suc n)
  suc  : ∀ {n} → Fin n → Fin (suc n)

data Vec {a} (A : Set a) : ℕ → Set a where
  []  : Vec A zero
  _∷_ : ∀ {n} (x : A) → Vec A n → Vec A (suc n)

data Fin∘suc : ℕ → Set where
  zero : ∀ {n} → Fin∘suc n
  suc  : ∀ {n} → Fin∘suc n → Fin∘suc (suc n)

_==_ : Bool → Bool → Bool
b₁ == b₂ = {!b₁ b₂!}

lookup : ∀ {a n} {A : Set a} → Vec A n → Fin n → A
lookup xs i = {!xs i!}

32-cases : Bool → Bool → Bool → Bool → Bool → Bool
32-cases a b c d e = {!a b c d e!}

No-splits-after-absurd-pattern-encountered :
  (n : ℕ) → Fin n → Fin n → Set
No-splits-after-absurd-pattern-encountered n i j = {!n i j!}

Dotted-patterns-are-not-split : ∀ n → Fin∘suc n → Set
Dotted-patterns-are-not-split n i = {!i n!}

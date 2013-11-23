{-# OPTIONS --copatterns --sized-types #-}

-- {-# OPTIONS -v tc.size:60 #-}

module SizedTypesMutual where

open import Common.Size

-- Syntax: Types, terms and contexts.

infixr 6 _⇒_
infixl 1 _,_

-- Types and contexts.

data Ty : Set where
  _⇒_ : (a b : Ty) → Ty

data Cxt : Set where
  _,_ : (Γ : Cxt) (a : Ty) → Cxt

-- Generic reversed Spines (last application available first).

data RSpine (V : Ty → Set) (a : Ty) : (c : Ty) → Set where
  _,_ : ∀ {b c} → RSpine V a (b ⇒ c) → V b → RSpine V a c

-- Functoriality for RSpine

mapRSp : ∀ {V W : Ty → Set} → (∀ {d} → V d → W d) → ∀ {a c} → RSpine V a c → RSpine W a c
mapRSp f (rs , r) = mapRSp f rs , f r

-- Values and environments

mutual
  data Env {i : Size} (Δ : Cxt) : Set where
    _,_ : ∀ {a} (ρ : Env {i = i} Δ) (v : Val {i = i} Δ a) → Env Δ

  data Val {i : Size} (Δ : Cxt) : (a : Ty) → Set where
    ne  : ∀ {j : Size< i}{a c} (vs : ValSpine {i = j} Δ a c) → Val Δ c
    lam : ∀ {a b}              (ρ : Env {i = i} Δ)           → Val Δ (a ⇒ b)

  ValSpine : {i : Size} (Δ : Cxt) (a c : Ty) → Set
  ValSpine {i = i} Δ = RSpine (Val {i = i} Δ)

-- Weakening

mutual
  weakEnv : ∀ {i Δ a} → Env {i = i} Δ → Env {i = i} (Δ , a)
  weakEnv {i = i} (ρ , v)  = weakEnv ρ , weakVal v

  weakVal : ∀ {i Δ a c} → Val {i = i} Δ c → Val {i = i} (Δ , a) c
  weakVal (ne {j = j} vs)  = ne (mapRSp (weakVal {i = j}) vs)
  weakVal (lam ρ)          = lam (weakEnv ρ)

-- This mutual block produces garbage size solutions
-- if solving is not done on a per-definition basis.

-- The reason is that the current solver assumes
-- that all size constraints live in (an extension of)
-- the same context (which is not true here).

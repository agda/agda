------------------------------------------------------------------------
-- Contexts, variables, substitutions, etc.
------------------------------------------------------------------------

{-# OPTIONS --universe-polymorphism #-}

-- Based on Conor McBride's "Outrageous but Meaningful Coincidences:
-- Dependent type-safe syntax and evaluation".

-- The contexts and variables are parametrised by a universe.

open import Universe

module Data.Context {u e} (Uni : Universe u e) where

open Universe.Universe Uni

open import Data.Product as Prod
open import Data.Unit
open import Function
open import Level

------------------------------------------------------------------------
-- Contexts and "types"

mutual

  -- Contexts.

  infixl 5 _▻_

  data Ctxt : Set (u ⊔ e) where
    ε   : Ctxt
    _▻_ : (Γ : Ctxt) (σ : Type Γ) → Ctxt

  -- Semantic types: maps from environments to universe codes.

  Type : Ctxt → Set (u ⊔ e)
  Type Γ = Env Γ → U

  -- Interpretation of contexts: environments.

  Env : Ctxt → Set e
  Env ε       = Lift ⊤
  Env (Γ ▻ σ) = Σ (Env Γ) λ γ → El (σ γ)

-- Type signature for variables, terms, etc.

Term-like : (ℓ : Level) → Set _
Term-like ℓ = (Γ : Ctxt) → Type Γ → Set ℓ

-- Semantic values: maps from environments to universe values.

Value : Term-like _
Value Γ σ = (γ : Env Γ) → El (σ γ)

------------------------------------------------------------------------
-- "Substitutions"

-- Semantic substitutions or context morphisms: maps from environments
-- to environments.

infixr 4 _⇨_

_⇨_ : Ctxt → Ctxt → Set _
Γ ⇨ Δ = Env Δ → Env Γ

-- Maps between types.

infixr 4 _⇨₁_

_⇨₁_ : ∀ {Γ} → Type Γ → Type Γ → Set _
σ ⇨₁ τ = ∀ {γ} → El (τ γ) → El (σ γ)

-- Application of substitutions to types.
--
-- Note that this operation is composition of functions. I have chosen
-- not to give a separate name to the identity substitution, which is
-- simply the identity function, nor to reverse composition of
-- substitutions, which is composition of functions.

infixl 8 _/_

_/_ : ∀ {Γ Δ} → Type Γ → Γ ⇨ Δ → Type Δ
σ / ρ = σ ∘ ρ

-- Application of substitutions to values.

infixl 8 _/v_

_/v_ : ∀ {Γ Δ σ} → Value Γ σ → (ρ : Γ ⇨ Δ) → Value Δ (σ / ρ)
v /v ρ = v ∘ ρ

-- Weakening.

wk : ∀ {Γ σ} → Γ ⇨ Γ ▻ σ
wk = proj₁

-- Extends a substitution with another value.

infixl 5 _►_

_►_ : ∀ {Γ Δ σ} (ρ : Γ ⇨ Δ) → Value Δ (σ / ρ) → Γ ▻ σ ⇨ Δ
_►_ = <_,_>

-- A substitution which only replaces the first "variable".

sub : ∀ {Γ σ} → Value Γ σ → Γ ▻ σ ⇨ Γ
sub v = id ► v

-- One can construct a substitution between two non-empty contexts by
-- supplying two functions, one which handles the last element and one
-- which handles the rest.

infixl 10 _↑_

_↑_ : ∀ {Γ Δ σ τ} (ρ : Γ ⇨ Δ) → σ / ρ ⇨₁ τ → Γ ▻ σ ⇨ Δ ▻ τ
_↑_ = Prod.map

-- Lifting.

infix 10 _↑

_↑ : ∀ {Γ Δ σ} (ρ : Γ ⇨ Δ) → Γ ▻ σ ⇨ Δ ▻ σ / ρ
ρ ↑ = ρ ↑ id

------------------------------------------------------------------------
-- Variables

-- Variables (de Bruijn indices).

infix 4 _∋_

data _∋_ : Term-like (u ⊔ e) where
  zero : ∀ {Γ σ}               → Γ ▻ σ ∋ σ / wk
  suc  : ∀ {Γ σ τ} (x : Γ ∋ σ) → Γ ▻ τ ∋ σ / wk

-- Interpretation of variables: a lookup function.

lookup : ∀ {Γ σ} → Γ ∋ σ → Value Γ σ
lookup zero    (γ , v) = v
lookup (suc x) (γ , v) = lookup x γ

-- Application of substitutions to variables.

infixl 8 _/∋_

_/∋_ : ∀ {Γ Δ σ} → Γ ∋ σ → (ρ : Γ ⇨ Δ) → Value Δ (σ / ρ)
x /∋ ρ = lookup x /v ρ

------------------------------------------------------------------------
-- Context extensions

mutual

  -- Context extensions.

  infixl 5 _▻_

  data Ctxt⁺ (Γ : Ctxt) : Set (u ⊔ e) where
    ε   : Ctxt⁺ Γ
    _▻_ : (Γ⁺ : Ctxt⁺ Γ) (σ : Type (Γ ++ Γ⁺)) → Ctxt⁺ Γ

  -- Appends a context extension to a context.

  infixl 5 _++_

  _++_ : (Γ : Ctxt) → Ctxt⁺ Γ → Ctxt
  Γ ++ ε        = Γ
  Γ ++ (Γ⁺ ▻ σ) = (Γ ++ Γ⁺) ▻ σ

mutual

  -- Application of substitutions to context extensions.

  infixl 8 _/⁺_

  _/⁺_ : ∀ {Γ Δ} → Ctxt⁺ Γ → Γ ⇨ Δ → Ctxt⁺ Δ
  ε        /⁺ ρ = ε
  (Γ⁺ ▻ σ) /⁺ ρ = Γ⁺ /⁺ ρ ▻ σ / ρ ↑⋆ Γ⁺

  -- N-ary lifting of substitutions.

  infixl 10 _↑⋆_

  _↑⋆_ : ∀ {Γ Δ} (ρ : Γ ⇨ Δ) → ∀ Γ⁺ → Γ ++ Γ⁺ ⇨ Δ ++ Γ⁺ /⁺ ρ
  ρ ↑⋆ ε        = ρ
  ρ ↑⋆ (Γ⁺ ▻ σ) = (ρ ↑⋆ Γ⁺) ↑

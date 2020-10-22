module Issue2858-nbe where

open import Agda.Builtin.List

data Ty : Set where
  α : Ty
  _↝_ : Ty → Ty → Ty

variable
  σ τ : Ty
  Γ Δ : List Ty

Scoped : Set₁
Scoped = Ty → List Ty → Set

data Var : Scoped where
  z : Var σ (σ ∷ Γ)
  s : Var σ Γ → Var σ (τ ∷ Γ)

record _⊆_ (Γ Δ : List Ty) : Set where
  field lookup : ∀ {σ} → Var σ Γ → Var σ Δ
open _⊆_ public

bind : Γ ⊆ Δ → (σ ∷ Γ) ⊆ (σ ∷ Δ)
lookup (bind ρ) z     = z
lookup (bind ρ) (s v) = s (lookup ρ v)

step : Γ ⊆ (σ ∷ Γ)
lookup step v = s v

infix mutual

  data Syn : Scoped
  data Chk : Scoped
  th^Syn : Γ ⊆ Δ → Syn σ Γ → Syn σ Δ
  th^Chk : Γ ⊆ Δ → Chk σ Γ → Chk σ Δ

  -- variable rule
  constructor
    var : Var σ Γ → Syn σ Γ
  th^Syn ρ (var v) = var (lookup ρ v)

  -- change of direction rules
  constructor
    emb : Syn σ Γ → Chk σ Γ
    cut : Chk σ Γ → Syn σ Γ
  th^Chk ρ (emb t) = emb (th^Syn ρ t)
  th^Syn ρ (cut c) = cut (th^Chk ρ c)

  -- function introduction and elimination
  constructor
    app : Syn (σ ↝ τ) Γ → Chk σ Γ → Syn τ Γ
    lam : Chk τ (σ ∷ Γ) → Chk (σ ↝ τ) Γ
  th^Syn ρ (app f t) = app (th^Syn ρ f) (th^Chk ρ t)
  th^Chk ρ (lam b) = lam (th^Chk (bind ρ) b)

-- Model construction

Val : Scoped
Val α       Γ = Syn α Γ
Val (σ ↝ τ) Γ = ∀ {Δ} → Γ ⊆ Δ → Val σ Δ → Val τ Δ


infix mutual

  reify   : ∀ σ → Val σ Γ → Chk σ Γ
  reflect : ∀ σ → Syn σ Γ → Val σ Γ

  -- base case
  reify   α t = emb t
  reflect α t = t

  -- arrow case
  reify   (σ ↝ τ) t = lam (reify τ (t step (reflect σ (var z))))
  reflect (σ ↝ τ) t = λ ρ v → reflect τ (app (th^Syn ρ t) (reify σ v))

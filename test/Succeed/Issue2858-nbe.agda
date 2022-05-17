module Issue2858-nbe where

open import Agda.Builtin.List

data Ty : Set where
  α : Ty
  _↝_ : Ty → Ty → Ty

variable
  σ τ : Ty
  Γ Δ Θ : List Ty

Scoped : Set₁
Scoped = Ty → List Ty → Set

data Var : Scoped where
  z : Var σ (σ ∷ Γ)
  s : Var σ Γ → Var σ (τ ∷ Γ)

record Ren (Γ Δ : List Ty) : Set where
  field lookup : ∀ {σ} → Var σ Γ → Var σ Δ
open Ren public

bind : Ren Γ Δ → Ren (σ ∷ Γ) (σ ∷ Δ)
lookup (bind ρ) z     = z
lookup (bind ρ) (s v) = s (lookup ρ v)

refl : Ren Γ Γ
lookup refl v = v

step : Ren Γ (σ ∷ Γ)
lookup step v = s v

_∘_ : Ren Δ Θ → Ren Γ Δ → Ren Γ Θ
lookup (ρ′ ∘ ρ) v = lookup ρ′ (lookup ρ v)

interleaved mutual

  data Syn : Scoped
  data Chk : Scoped
  th^Syn : Ren Γ Δ → Syn σ Γ → Syn σ Δ
  th^Chk : Ren Γ Δ → Chk σ Γ → Chk σ Δ

  -- variable rule
  data _ where
    var : Var σ Γ → Syn σ Γ
  th^Syn ρ (var v) = var (lookup ρ v)

  -- change of direction rules
  data _ where
    emb : Syn σ Γ → Chk σ Γ
    cut : Chk σ Γ → Syn σ Γ
  th^Chk ρ (emb t) = emb (th^Syn ρ t)
  th^Syn ρ (cut c) = cut (th^Chk ρ c)

  -- function introduction and elimination
  data _ where
    app : Syn (σ ↝ τ) Γ → Chk σ Γ → Syn τ Γ
    lam : Chk τ (σ ∷ Γ) → Chk (σ ↝ τ) Γ
  th^Syn ρ (app f t) = app (th^Syn ρ f) (th^Chk ρ t)
  th^Chk ρ (lam b) = lam (th^Chk (bind ρ) b)

-- Model construction

Val : Scoped
Val α       Γ = Syn α Γ
Val (σ ↝ τ) Γ = ∀ {Δ} → Ren Γ Δ → Val σ Δ → Val τ Δ

th^Val : Ren Γ Δ → Val σ Γ → Val σ Δ
th^Val {σ = α}     ρ t = th^Syn ρ t
th^Val {σ = σ ↝ τ} ρ t = λ ρ′ → t (ρ′ ∘ ρ)

interleaved mutual

  reify   : ∀ σ → Val σ Γ → Chk σ Γ
  reflect : ∀ σ → Syn σ Γ → Val σ Γ

  -- base case
  reify   α t = emb t
  reflect α t = t

  -- arrow case
  reify   (σ ↝ τ) t = lam (reify τ (t step (reflect σ (var z))))
  reflect (σ ↝ τ) t = λ ρ v → reflect τ (app (th^Syn ρ t) (reify σ v))

record Env (Γ Δ : List Ty) : Set where
  field lookup : ∀ {σ} → Var σ Γ → Val σ Δ
open Env public

th^Env : Ren Δ Θ → Env Γ Δ → Env Γ Θ
lookup (th^Env ρ vs) v = th^Val ρ (lookup vs v)

placeholders : Env Γ Γ
lookup placeholders v = reflect _ (var v)

extend : Env Γ Δ → Val σ Δ → Env (σ ∷ Γ) Δ
lookup (extend ρ t) z     = t
lookup (extend ρ t) (s v) = lookup ρ v

interleaved mutual

  eval^Syn : Env Γ Δ → Syn σ Γ → Val σ Δ
  eval^Chk : Env Γ Δ → Chk σ Γ → Val σ Δ

  -- variable
  eval^Syn vs (var v) = lookup vs v

  -- change of direction
  eval^Syn vs (cut t) = eval^Chk vs t
  eval^Chk vs (emb t) = eval^Syn vs t

  -- function introduction & elimination
  eval^Syn vs (app f t) = eval^Syn vs f refl (eval^Chk vs t)
  eval^Chk vs (lam b)   = λ ρ v → eval^Chk (extend (th^Env ρ vs) v) b

interleaved mutual

  norm^Syn : Syn σ Γ → Chk σ Γ
  norm^Chk : Chk σ Γ → Chk σ Γ

  norm^Syn t = norm^Chk (emb t)
  norm^Chk t = reify _ (eval^Chk placeholders t)

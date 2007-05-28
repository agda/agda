module Lambda where

open import Prelude
open import Star
open import Examples
open import Modal

-- Environments

data Ty : Set where
  nat : Ty
  _⟶_ : Ty -> Ty -> Ty

Ctx : Set
Ctx = List Ty

Var : Ctx -> Ty -> Set
Var Γ τ = Any (_==_ τ) Γ

vzero : {τ : Ty} {Γ : Ctx} -> Var (τ • Γ) τ
vzero = done refl • ε

vsuc : {σ τ : Ty} {Γ : Ctx} -> Var Γ τ -> Var (σ • Γ) τ
vsuc v = step • v

data Tm : Ctx -> Ty -> Set where
  var : forall {Γ τ}   -> Var Γ τ -> Tm Γ τ
  zz  : forall {Γ}     -> Tm Γ nat
  ss  : forall {Γ}     -> Tm Γ (nat ⟶ nat)
  λ   : forall {Γ σ τ} -> Tm (σ • Γ) τ -> Tm Γ (σ ⟶ τ)
  _$_ : forall {Γ σ τ} -> Tm Γ (σ ⟶ τ) -> Tm Γ σ -> Tm Γ τ

ty⟦_⟧ : Ty -> Set
ty⟦ nat   ⟧ = Nat
ty⟦ σ ⟶ τ ⟧ = ty⟦ σ ⟧ -> ty⟦ τ ⟧

Env : Ctx -> Set
Env = All ty⟦_⟧

_[_] : forall {Γ τ} -> Env Γ -> Var Γ τ -> ty⟦ τ ⟧
ρ [ x ] with lookup x ρ
ρ [ x ] | result _ refl v = v

⟦_⟧_ : forall {Γ τ} -> Tm Γ τ -> Env Γ -> ty⟦ τ ⟧
⟦ var x ⟧ ρ = ρ [ x ]
⟦ zz    ⟧ ρ = zero
⟦ ss    ⟧ ρ = suc
⟦ λ t   ⟧ ρ = \x -> ⟦ t ⟧ (check x • ρ)
⟦ s $ t ⟧ ρ = (⟦ s ⟧ ρ) (⟦ t ⟧ ρ)

tm_one : Tm ε nat
tm_one = ss $ zz

tm_id : Tm ε (nat ⟶ nat)
tm_id = λ (var (done refl • ε))

tm    : Tm ε nat
tm    = tm_id $ tm_one

tm_twice : Tm ε ((nat ⟶ nat) ⟶ (nat ⟶ nat))
tm_twice = λ (λ (f $ (f $ x)))
  where Γ : Ctx
        Γ = nat • (nat ⟶ nat) • ε
        f : Tm Γ (nat ⟶ nat)
        f = var (vsuc vzero)
        x : Tm Γ nat
        x = var vzero

sem : {τ : Ty} -> Tm ε τ -> ty⟦ τ ⟧
sem e = ⟦ e ⟧ ε

one : Nat
one = sem tm

twice : (Nat -> Nat) -> (Nat -> Nat)
twice = sem tm_twice

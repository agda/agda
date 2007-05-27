
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
Var Γ τ = Any (\σ -> σ == τ) Γ

data Tm : Ctx -> Ty -> Set where
  var : forall {Γ τ} -> Var Γ τ -> Tm Γ τ
  zz  : forall {Γ} -> Tm Γ nat
  ss  : forall {Γ} -> Tm Γ (nat ⟶ nat)
  λ   : forall {Γ σ τ} -> Tm (σ • Γ) τ -> Tm Γ (σ ⟶ τ)
  _$_ : forall {Γ σ τ} -> Tm Γ (σ ⟶ τ) -> Tm Γ σ -> Tm Γ τ

ty⟦_⟧ : Ty -> Set
ty⟦ nat   ⟧ = Nat
ty⟦ σ ⟶ τ ⟧ = ty⟦ σ ⟧ -> ty⟦ τ ⟧

data EStep : Rel Ctx where
  val : forall {Γ τ} -> ty⟦ τ ⟧ -> EStep (τ • Γ) Γ

Env : Ctx -> Set
Env = All ty⟦_⟧

_[_] : forall {Γ τ} -> Env Γ -> Var Γ τ -> ty⟦ τ ⟧
(check v • ρ) [ done refl • ε ] = v
(check _ • ρ) [ step      • x ] = ρ [ x ]

⟦_⟧_ : forall {Γ τ} -> Tm Γ τ -> Env Γ -> ty⟦ τ ⟧
⟦ var x ⟧ ρ = ρ [ x ]
⟦ zz    ⟧ ρ = zero
⟦ ss    ⟧ ρ = suc
⟦ λ t   ⟧ ρ = \x -> ⟦ t ⟧ (check x • ρ)
⟦ s $ t ⟧ ρ = (⟦ s ⟧ ρ) (⟦ t ⟧ ρ)

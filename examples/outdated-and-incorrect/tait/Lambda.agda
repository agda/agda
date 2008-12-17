
module Lambda where

open import Prelude

-- Simply typed λ-calculus

infixr 70 _⟶_

data Type : Set where
  ι   : Type
  _⟶_ : Type -> Type -> Type

Ctx : Set
Ctx = List Type

infixl 80 _•_
infix  20  ƛ_

data Term : Ctx -> Type -> Set where
  vz  : forall {Γ τ  } -> Term (Γ , τ) τ
  wk  : forall {Γ σ τ} -> Term Γ τ -> Term (Γ , σ) τ
  _•_ : forall {Γ σ τ} -> Term Γ (σ ⟶ τ) -> Term Γ σ -> Term Γ τ
  ƛ_  : forall {Γ σ τ} -> Term (Γ , σ) τ -> Term Γ (σ ⟶ τ)

Terms : Ctx -> Ctx -> Set
Terms Γ Δ = All (Term Γ) Δ

infixl 60 _◄_
infixr 70 _⇒_

_⇒_ : Ctx -> Type -> Type
ε       ⇒ τ = τ
(Δ , σ) ⇒ τ = Δ ⇒ σ ⟶ τ

infixl 80 _•ˢ_

_•ˢ_ : {Γ Δ : Ctx}{τ : Type} -> Term Γ (Δ ⇒ τ) -> Terms Γ Δ -> Term Γ τ
t •ˢ ∅        = t
t •ˢ (us ◄ u) = t •ˢ us • u

Var : Ctx -> Type -> Set
Var Γ τ = τ ∈ Γ

var : forall {Γ τ} -> Var Γ τ -> Term Γ τ
var hd     = vz
var (tl x) = wk (var x)

vzero : forall {Γ τ} -> Var (Γ , τ) τ
vzero = hd

vsuc : forall {Γ σ τ} -> Var Γ τ -> Var (Γ , σ) τ
vsuc = tl
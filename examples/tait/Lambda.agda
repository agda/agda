
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
infix  20  λ_

data Var : Ctx -> Type -> Set where
  vz : {Γ : Ctx}{τ : Type} -> Var (Γ , τ) τ
  vs : {Γ : Ctx}{σ τ : Type} -> Var Γ τ -> Var (Γ , σ) τ

data Term (Γ : Ctx) : Type -> Set where
  var : {τ : Type} -> Var Γ τ -> Term Γ τ
  _•_ : {σ τ : Type} -> Term Γ (σ ⟶ τ) -> Term Γ σ -> Term Γ τ
  λ_  : {σ τ : Type} -> Term (Γ , σ) τ -> Term Γ (σ ⟶ τ)

data Terms (Γ : Ctx) : Ctx -> Set where
  ∅   : Terms Γ ε
  _◄_ : {Δ : Ctx}{τ : Type} -> Terms Γ Δ -> Term Γ τ -> Terms Γ (Δ , τ)

infixl 60 _◄_
infixr 70 _⇒_

_⇒_ : Ctx -> Type -> Type
ε       ⇒ τ = τ
(Δ , σ) ⇒ τ = Δ ⇒ σ ⟶ τ

infixl 80 _•ˢ_

_•ˢ_ : {Γ Δ : Ctx}{τ : Type} -> Term Γ (Δ ⇒ τ) -> Terms Γ Δ -> Term Γ τ
t •ˢ ∅        = t
t •ˢ (us ◄ u) = t •ˢ us • u


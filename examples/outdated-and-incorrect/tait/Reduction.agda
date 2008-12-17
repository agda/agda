
module Reduction where

open import Prelude
open import Lambda
open import Subst
open import Trans

infix 10 _⟶β_

data _⟶β_ : forall {Γ τ} -> (t u : Term Γ τ) -> Set where
  β   : forall {Γ σ τ}{t : Term (Γ , σ) τ} Δ {u : Term (Γ ++ Δ) σ} ->
        (ƛ t) ↑ Δ • u ⟶β t ↑ Δ / [ Δ ⟵ u ]
  wk⟶ : forall {Γ σ τ}{t₁ t₂ : Term Γ τ} ->
        t₁ ⟶β t₂ -> wk {σ = σ} t₁ ⟶β wk t₂
  •⟶L : forall {Γ σ τ}{t₁ t₂ : Term Γ (σ ⟶ τ)}{u : Term Γ σ} ->
        t₁ ⟶β t₂ -> t₁ • u ⟶β t₂ • u
  •⟶R : forall {Γ σ τ}{t : Term Γ (σ ⟶ τ)}{u₁ u₂ : Term Γ σ} ->
        u₁ ⟶β u₂ -> t • u₁ ⟶β t • u₂
  ƛ⟶  : forall {Γ σ τ}{t₁ t₂ : Term (Γ , σ) τ} ->
        t₁ ⟶β t₂ -> ƛ t₁ ⟶β ƛ t₂

_⟶β*_ : {Γ : Ctx}{τ : Type}(x y : Term Γ τ) -> Set
x ⟶β* y = [ _⟶β_ ]* x y

↑⟶β : {Γ : Ctx}(Δ : Ctx){τ : Type}{t u : Term Γ τ} ->
         t ⟶β u ->  t ↑ Δ ⟶β u ↑ Δ
↑⟶β ε       r = r
↑⟶β (Δ , σ) r = wk⟶ (↑⟶β Δ r)

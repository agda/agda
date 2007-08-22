
module Reduction where

open import Prelude
open import Lambda
open import Subst
open import Trans

infix 10 _⟶β_

data _⟶β_ {Γ : Ctx} : {τ : Type} -> (t u : Term Γ τ) -> Set where
  β   : {σ τ : Type}{t : Term (Γ , σ) τ}{u : Term Γ σ} ->
        (λ t) • u ⟶β t [ u ]
  •⟶L : {σ τ : Type}{t₁ t₂ : Term Γ (σ ⟶ τ)}{u : Term Γ σ} ->
        t₁ ⟶β t₂ -> t₁ • u ⟶β t₂ • u
  •⟶R : {σ τ : Type}{t : Term Γ (σ ⟶ τ)}{u₁ u₂ : Term Γ σ} ->
        u₁ ⟶β u₂ -> t • u₁ ⟶β t • u₂
  λ⟶  : {σ τ : Type}{t₁ t₂ : Term (Γ , σ) τ} ->
        t₁ ⟶β t₂ -> λ t₁ ⟶β λ t₂

_⟶β*_ : {Γ : Ctx}{τ : Type}(x y : Term Γ τ) -> Set
x ⟶β* y = [ _⟶β_ ]* x y

wk⟶β : {Γ : Ctx}{σ τ : Type}(x : Var Γ σ){t₁ t₂ : Term (Γ - x) τ} ->
       t₁ ⟶β t₂ -> wk x t₁ ⟶β wk x t₂
wk⟶β x (β {t = t}) = subst (_⟶β_ _) (lem-wk-[]' x t) β
wk⟶β x (•⟶L r)     = •⟶L (wk⟶β x r)
wk⟶β x (•⟶R r)     = •⟶R (wk⟶β x r)
wk⟶β x (λ⟶  r)     = λ⟶ (wk⟶β (vs x) r)


↑⟶β : {Γ : Ctx}(Δ : Ctx){τ : Type}{t u : Term Γ τ} ->
         t ⟶β u ->  t ↑ Δ ⟶β u ↑ Δ
↑⟶β ε       r = r
↑⟶β (Δ , σ) r = wk⟶β vz (↑⟶β Δ r)


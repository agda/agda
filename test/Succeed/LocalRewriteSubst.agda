{-# OPTIONS --local-rewriting #-}

open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite
open import Agda.Builtin.Nat

module LocalRewriteSubst where

module Utils where
  infixr 4 _∙_

  private variable
    A B C D : Set _
    x y z w : A

  sym : x ≡ y → y ≡ x
  sym refl = refl

  _∙_ : x ≡ y → y ≡ z → x ≡ z
  refl ∙ q = q

  ap : (f : A → B) → x ≡ y → f x ≡ f y
  ap f refl = refl

  ap₂ : (f : A → B → C) → x ≡ y → z ≡ w → f x z ≡ f y w
  ap₂ f refl refl = refl
open Utils

Ctx = Nat

pattern _▷ Γ = suc Γ
pattern •    = zero

variable
  Γ Δ Θ : Ctx

data Var : Nat → Set where
  vz : Var (Γ ▷)
  vs : Var Γ → Var (Γ ▷)

data Tm : Nat → Set where
  var : Var Γ → Tm Γ
  lam : Tm (Γ ▷) → Tm Γ
  app : Tm Γ → Tm Γ → Tm Γ

data Tms (F : Ctx → Set) (Δ : Ctx) : Ctx → Set where
  ε   : Tms F Δ •
  _,_ : Tms F Δ Γ → F Δ → Tms F Δ (Γ ▷)

variable
  x y z : Var _
  t u v : Tm _
  δ σ τ : Tms _ _ _

module _ {F : Ctx → Set} where
  lookup : Var Γ → Tms F Δ Γ → F Δ
  lookup vz     (δ , t) = t
  lookup (vs x) (δ , t) = lookup x δ

module FSubst
  (F : Ctx → Set)
  (fz : ∀ {Γ} → F (Γ ▷))
  (fs : ∀ {Γ} → F Γ → F (Γ ▷))
  (F↑ : ∀ {Γ} → F Γ → Tm Γ)
  where

  _[_] : Tm Γ → Tms F Δ Γ → Tm Δ
  _⁺   : Tms F Δ Γ → Tms F (Δ ▷) Γ
  _^   : Tms F Δ Γ → Tms F (Δ ▷) (Γ ▷)

  var x   [ δ ] = F↑ (lookup x δ)
  lam t   [ δ ] = lam (t [ δ ^ ])
  app t u [ δ ] = app (t [ δ ]) (u [ δ ])

  δ ^ = (δ ⁺) , fz

  ε       ⁺ = ε
  (δ , t) ⁺ = (δ ⁺) , fs t

  id : Tms F Γ Γ
  id {Γ = •}   = ε
  id {Γ = Γ ▷} = id ^

  module IdProofs
    (↑F  : ∀ {Γ} → Var Γ → F Γ)
    (@rew ↑vz : ∀ {Γ} → ↑F (vz {Γ = Γ}) ≡ fz)
    (↑vs : ∀ {Γ} {x : Var Γ} → ↑F (vs x) ≡ fs (↑F x))
    (@rew ↑F↑ : ∀ {Γ} {x : Var Γ} → F↑ (↑F x) ≡ var x)
    where

    lookup-⁺ : lookup x (δ ⁺) ≡ fs (lookup x δ)
    lookup-id : lookup x id ≡ ↑F x

    lookup-⁺ {x = vz}   {δ = δ , t} = refl
    lookup-⁺ {x = vs x} {δ = δ , t} = lookup-⁺ {x = x} {δ = δ}

    lookup-id {x = vz}   = refl
    lookup-id {x = vs x} =
      lookup-⁺ {x = x} {δ = id} ∙ ap fs lookup-id ∙ sym ↑vs

    [id] : t [ id ] ≡ t
    [id] {t = var x}   = ap F↑ lookup-id
    [id] {t = lam t}   = ap lam [id]
    [id] {t = app t u} = ap₂ app [id] [id]

module Ren   = FSubst Var vz vs var
module Subst = FSubst Tm (var vz) (Ren._[ Ren.id Ren.⁺ ]) (λ t → t)

module RenIdProofs   = Ren.IdProofs (λ x → x) refl refl refl
module SubstIdProofs = Subst.IdProofs var refl (λ {_} {x} →
  ap var (sym (RenIdProofs.lookup-⁺ {x = x} ∙ ap vs (RenIdProofs.lookup-id))))
  refl

-- TODO: Composition

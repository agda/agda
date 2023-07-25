{-# OPTIONS --allow-unsolved-metas --large-indices #-}
module _ where

open import Agda.Builtin.Nat
open import Agda.Builtin.List
open import Agda.Builtin.Unit
open import Agda.Builtin.Sigma

_×_ : Set → Set → Set
A × B = Σ A λ _ → B

data Vec (A : Set) : Nat → Set where
  []  : Vec A 0
  _∷_ : ∀ {n} → A → Vec A n → Vec A (suc n)

data All {A : Set} (P : A → Set) : List A → Set where
  []  : All P []
  _∷_ : ∀ {x xs} → P x → All P xs → All P (x ∷ xs)

data Ty : Set where

module Code where

  Schema : List Nat → Set
  Schema = All (λ k → Vec Ty k × Ty)

  data Binder : Set where
    bound unbound : Binder

  Shape : Nat → Set
  Shape n = List (Vec Binder n)

  data Code : Set₁ where
    sg : (A : Set) → (A → Code) → Code
    node : (n : Nat) (shape : Shape n) (wt : Vec Ty n → All (λ _ → Ty) shape → Ty → Set) → Code

module Ctx where
  infixr 4 _,_

  data Ctx : Set where
    ∅ : Ctx
    _,_ : Ctx → Ty → Ctx

  _<><_ : Ctx → List Ty → Ctx
  Γ <>< [] = Γ
  Γ <>< (t ∷ ts) = (Γ , t) <>< ts

module Typed (code : Code.Code) where
  open Code
  open Ctx

  visible : ∀ {n} → Vec Binder n → Vec Ty n → List Ty
  visible []             []       = []
  visible (bound ∷ bs)   (t ∷ ts) = t ∷ visible bs ts
  visible (unbound ∷ bs) (_ ∷ ts) = visible bs ts

  mutual
    data Tm (Γ : Ctx) : Ty → Set where

    data Con (Γ : Ctx) (t : Ty) : Code → Set where
      sg : ∀ {A c} x → Con Γ t (c x) → Con Γ t (sg A c)
      node : ∀ {n shape wt} (ts₀ : Vec Ty n) {ts : All (λ _ → Ty) shape} (es : Children Γ ts₀ ts) →
        {{_ : wt ts₀ ts t}} → Con Γ t (node n shape wt)

    data Children (Γ : Ctx) {n : Nat} (ts₀ : Vec Ty n) : {sh : Shape n} → All (λ _ → Ty) sh → Set where
      [] : Children Γ ts₀ []
      _∷_ : ∀ {bs sh t ts} → Tm (Γ <>< visible bs ts₀) t → Children Γ ts₀ {sh} ts → Children Γ ts₀ {bs ∷ sh} (t ∷ ts)

  module Sem₀ (P : Ctx → Ty → Set) where
    children : ∀ {n} (Γ : Ctx) (ts₀ : Vec Ty n) (shape : List (Vec Binder n)) (ts : All (λ _ → Ty) shape) → Set
    children Γ ts₀ [] [] = ⊤
    children Γ ts₀ (bs ∷ bss) (t ∷ ts) = P (Γ <>< visible bs ts₀ ) t × children Γ ts₀ bss ts

    aux : Code → Set
    aux (sg A k) = (x : A) → aux (k x)
    aux (node n shape wt) = ∀ {Γ t} {ts₀ ts} → children Γ ts₀ shape ts → wt ts₀ ts t → P Γ t

  Sem : (P : Ctx → Ty → Set) → Set
  Sem P = Sem₀.aux P code

open Code

data Phase : Set where
  input : Phase

data `STLC : Phase → Set where
  `let : `STLC input

STLC : Phase → Code
STLC p = sg (`STLC p) aux
  where
    aux : `STLC p → Code
    aux `let = node 1 ((bound ∷ []) ∷ []) λ { (t₀ ∷ _) (t₁ ∷ _) t → ⊤ }

open Ctx

open Typed (STLC input) using (Sem)

ap : Sem λ Γ t → Nat
ap = λ where `let → {!!}

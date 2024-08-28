{-# OPTIONS --without-K #-}

module _ where

open import Agda.Primitive using (Level; _⊔_; lzero; lsuc)
infixl 1 _,_
infixl 2 _▻_
infixl 3 _‘’_
infixl 3 _‘’₁_

record Σ {ℓ ℓ′} (A : Set ℓ) (P : A → Set ℓ′) : Set (ℓ ⊔ ℓ′) where
  constructor _,_
  field fst : A
  field snd : P fst
record ⊤ {ℓ : Level} : Set ℓ where
  constructor tt

data Context : Set
data Type : Context → Set

data Context where
  ε : Context
  _▻_ : (Γ : Context) → Type Γ → Context

data Term : {Γ : Context} → Type Γ → Set

data Type where
  _‘’_ : ∀ {Γ A} → Type (Γ ▻ A) → Term {Γ} A → Type Γ
  _‘’₁_ : ∀ {Γ A B} → Type (Γ ▻ A ▻ B) → (a : Term {Γ} A) → Type (Γ ▻ B ‘’ a)
  ‘Context’ : ∀ {Γ} → Type Γ
  ‘Type’ : ∀ {Γ} → Type (Γ ▻ ‘Context’)

data Term where

Context⇓ : (Γ : Context) → Set
Type⇓ : {Γ : Context} → Type Γ → Context⇓ Γ → Set

Context⇓ ε = ⊤
Context⇓ (Γ ▻ T) = Σ (Context⇓ Γ) (Type⇓ {Γ} T)

Term⇓ : ∀ {Γ : Context} {T : Type Γ} → Term T → (Γ⇓ : Context⇓ Γ) → Type⇓ T Γ⇓

Type⇓ ‘Context’ Γ⇓ = Context
Type⇓ ‘Type’ Γ⇓ = Type (Σ.snd Γ⇓)
Type⇓ (T ‘’ a) Γ⇓ = Type⇓ T (Γ⇓ , Term⇓ a Γ⇓)
-- Swapping the above two lines results in success
Type⇓ (T ‘’₁ a) Γ⇓ = Type⇓ T (Σ.fst Γ⇓ , Term⇓ a (Σ.fst Γ⇓) , Σ.snd Γ⇓)
{- /home/jgross/Documents/GitHub/lob/internal/term-bug2.agda:45,63-71
Γ != Γ ▻ A of type Context
when checking that the expression Σ.snd Γ⇓ has type
Type⇓ B (Σ.fst Γ⇓ , Term⇓ a (Σ.fst Γ⇓)) -}

Term⇓ ()

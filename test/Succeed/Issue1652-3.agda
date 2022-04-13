{- Example by Guillaume Brunerie, 17-11-2015 -}

{-# OPTIONS --rewriting --cubical-compatible #-}

open import Agda.Primitive

postulate
  _↦_ : ∀ {i} {A : Set i} → A → A → Set i
  idr : ∀ {i} {A : Set i} {a : A} → a ↦ a
{-# BUILTIN REWRITE _↦_ #-}

infixr 3 _==_

data _==_ {i} {A : Set i} (a : A) : A → Set i where
  idp : a == a

PathOver : ∀ {i j} {A : Set i} (B : A → Set j)
  {x y : A} (p : x == y) (u : B x) (v : B y) → Set j
PathOver B idp u v = (u == v)

syntax PathOver B p u v =
  u == v [ B ↓ p ]

postulate
  PathOver-rewr : ∀ {i j} {A : Set i} {B : Set j} {x y : A} (p : x == y) (u v : B) →
    (PathOver (λ _ → B) p u v) ↦ (u == v)
  {-# REWRITE PathOver-rewr #-}

ap : ∀ {i j} {A : Set i} {B : A → Set j} (f : (a : A) → B a) {x y : A}
  → (p : x == y) → PathOver B p (f x) (f y)
ap f idp = idp


module _ {i j k} {A : Set i} {B : Set j} {C : Set k} (g : B → C) (f : A → B) where

  ∘ap : {x y : A} (p : x == y) →
    ap g (ap f p) ↦ ap (λ x → g (f x)) p
  ∘ap idp = idr
  {-# REWRITE ∘ap #-}

  ap∘ : {x y : A} (p : x == y) →
    ap (λ x → g (f x)) p ↦ ap g (ap f p)
  ap∘ p = idr

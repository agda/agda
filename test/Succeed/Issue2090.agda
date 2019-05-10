{-# OPTIONS --rewriting --confluence-check #-}

open import Agda.Primitive

postulate
  _↦_ : ∀ {i} {A : Set i} → A → A → Set i
  idr : ∀ {i} {A : Set i} {a : A} → a ↦ a
{-# BUILTIN REWRITE _↦_ #-}

postulate
  _==_ : ∀ {i} {A : Set i} → A → A → Set i
  idp : ∀ {i} {A : Set i} {a : A} → a == a

postulate
  HetEq : ∀ {i} {A B : Set i} (e : A == B) (a : A) (b : B) → Set i
  HetEq↦ : ∀ {i} {A : Set i} (a b : A) → HetEq idp a b ↦ (a == b)
  {-# REWRITE HetEq↦ #-}

HetEq↦2 : ∀ {i j} {A : Set i} {B : Set j} (u v : A → B) → HetEq idp u v ↦ (u == v)
HetEq↦2 u v = idr

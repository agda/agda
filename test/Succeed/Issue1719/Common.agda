{-# OPTIONS --cubical-compatible --rewriting --confluence-check #-}

module Issue1719.Common where

ofType : ∀ {i} (A : Set i) → A → A
ofType A x = x

syntax ofType A x = x :> A

infixr 3 ofType

postulate
  _↦_ : ∀ {i} {A : Set i} → A → A → Set i
  idr : ∀ {i} {A : Set i} {a : A} → a ↦ a
{-# BUILTIN REWRITE _↦_ #-}

infixr 3 _==_

data _==_ {i} {A : Set i} (a : A) : A → Set i where
  idp : a == a

HetEq : ∀ {i} {A B : Set i} (e : A == B) (a : A) (b : B) → Set i
HetEq idp a b = (a == b)

PathOver : ∀ {i j} {A : Set i} (B : A → Set j)
  {x y : A} (p : x == y) (u : B x) (v : B y) → Set j
PathOver B idp u v = (u == v)

syntax PathOver B p u v =
  u == v [ B ↓ p ]

postulate
  PathOver-rewr : ∀ {i j} {A : Set i} {B : Set j} {x y : A} (p : x == y) (u v : B) →
    (PathOver (λ _ → B) p u v) ↦ (u == v)
  {-# REWRITE PathOver-rewr #-}

-- Note that this is both [ap] and [apd], as a [PathOver] in a constant family
-- reduces to the usual identity type.
ap : ∀ {i j} {A : Set i} {B : A → Set j} (f : (a : A) → B a) {x y : A}
  → (p : x == y) → PathOver B p (f x) (f y)
ap f idp = idp

postulate
  ap-cst : ∀ {i j} {A : Set i} {B : Set j} (b : B) {x y : A} (p : x == y) →
    ap (λ _ → b) p ↦ idp
  {-# REWRITE ap-cst #-}

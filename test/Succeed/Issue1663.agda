{-# OPTIONS --without-K --rewriting --confluence-check #-}

postulate
  _↦_ : ∀ {i} {A : Set i} → A → A → Set i
  idr : ∀ {i} {A : Set i} {a : A} → a ↦ a
{-# BUILTIN REWRITE _↦_ #-}

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


postulate
  Circle : Set
  base : Circle
  loop : base == base

module _ {i} {P : Circle → Set i} (base* : P base) (loop* : base* == base* [ P ↓ loop ])
 where
  postulate
    Circle-elim : (x : Circle) → P x
    Circle-base-β : Circle-elim base ↦ base*
    {-# REWRITE Circle-base-β #-}
    Circle-loop-β : ap Circle-elim loop ↦ loop*
    {-# REWRITE Circle-loop-β #-}

idCircle : Circle → Circle
idCircle = Circle-elim base loop

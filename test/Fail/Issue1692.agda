-- Andreas, 2015-11-18, issue 1692 reported by m0davis

-- {-# OPTIONS -v tc.with.top:20 #-}

open import Common.Level
open import Common.Equality
open import Common.Product

postulate
  Key   : Set
  Value : Key → Set
  anyOf : ∀{A : Set} → A → A → A

data Tree : Set where
  node : (k : Key) (v : Value k) → Tree

data _∼_∈_ ( k : Key ) ( v : Value k ) : Tree → Set where
  here :  k ∼ v ∈ node k v

postulate
  k₁≡k₂ : ∀ ( k₁ k₂ : Key ) → k₁ ≡ k₂
  ∈→v₁≡v₂ : ∀ { k } { v₁ v₂ : Value k } → k ∼ v₁ ∈ node k v₂ → v₁ ≡ v₂

lem : ( t₁ t₂ : Tree )
      ( t₁→t₂ : ∀ {k} {v : Value k} → k ∼ v ∈ t₁ → k ∼ v ∈ t₂ )
      ( t₂→t₁ : ∀ {k} {v : Value k} → k ∼ v ∈ t₂ → k ∼ v ∈ t₁ ) →
      ∃ λ t → ∀ {k} {v : Value k} → k ∼ v ∈ t → k ∼ v ∈ t
lem (node k₁ v₁) (node k₂ v₂) t₁→t₂ t₂→t₁ rewrite k₁≡k₂ k₁ k₂
     | ∈→v₁≡v₂ (t₁→t₂ here) -- equivalent to v₂ ≡ v₁
     = _ , anyOf t₁→t₂ t₂→t₁

-- PROBLEM WAS:

-- When the second rewrite expression is commented-out, then we get the following types:
   {-
     t₂→t₁    : {k : Key} {v : Value k} →
                k ∼ v ∈ node k₂ v₂ → k ∼ v ∈ node k₂ v₁
     t₁→t₂    : {k : Key} {v : Value k} →
                k ∼ v ∈ node k₂ v₁ → k ∼ v ∈ node k₂ v₂
   -}
-- With both rewrite expressions, we get:
   {-
     t₂→t₁    : {k : Key} {v : Value k} →
                k ∼ v ∈ node k₂ v₂ → k ∼ v ∈ node k₂ v₂
     t₁→t₂    : {k : Key} {v : Value k} →
                k ∼ v ∈ node k₂ v₁ → k ∼ v ∈ node k₂ v₂
   -}
-- The unexpected behavior here is that v₁ has been rewritten to v₂ in t₂→t₁ but not in t₁→t₂.

-- Should be symmetric now, test case passes.

-- Dual case:

lem′ : ( t₁ t₂ : Tree )
      ( t₁→t₂ : ∀ {k} {v : Value k} → k ∼ v ∈ t₁ → k ∼ v ∈ t₂ )
      ( t₂→t₁ : ∀ {k} {v : Value k} → k ∼ v ∈ t₂ → k ∼ v ∈ t₁ ) →
      ∃ λ t → ∀ {k} {v : Value k} → k ∼ v ∈ t → k ∼ v ∈ t
lem′ (node k₁ v₁) (node k₂ v₂) t₁→t₂ t₂→t₁ rewrite k₁≡k₂ k₁ k₂
     | ∈→v₁≡v₂ (t₂→t₁ here) -- equivalent to v₁ ≡ v₂
     = _ , anyOf t₁→t₂ t₂→t₁

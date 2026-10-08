-- Andreas, 2026-10-08, issue #7972
-- Mimer should solve goals whose type unifies with a hint
-- only after postponing constraints.

module Issue7972 (A : Set) (z : A) (s : A → A) where

thm : Set₁
thm = Set
  where
    N : A → Set₁
    N a = (X : A → Set) → X z → (∀ n → X n → X (s n)) → X a
    n-s : ∀ n → N n → N (s n)
    n-s x h X x₁ x₂ = {!!}  -- Expected: x₂ x (h X x₁ x₂)

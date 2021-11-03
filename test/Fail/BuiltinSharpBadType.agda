
data ⊥ : Set where

postulate
  ∞  : ∀ {a} → Set a → Set a
  ♯_ : ∀ {a} {A : Set a} → (A → ⊥) → ∞ A
  ♭  : ∀ {a} {A : Set a} → ∞ A → A → ⊥

{-# BUILTIN INFINITY ∞  #-}
{-# BUILTIN SHARP    ♯_ #-}
{-# BUILTIN FLAT     ♭  #-}

-- Issue #5610: with these bad types for sharp and flat, we can prove
-- false. The reason is that ∞ is assumed to be strictly-positive in
-- the positivity checker (even guarding positive). So making ∞ A
-- isomorphic to A → ⊥ will be contradictory to this assumption.

data D : Set where
  wrap : ∞ D → D

lam : (D → ⊥) → D
lam f = wrap (♯ f)

app : D → D → ⊥
app (wrap g) d = ♭ g d

delta : D
delta = lam (λ x → app x x)

omega : ⊥
omega = app delta delta

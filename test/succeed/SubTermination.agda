-- {-# OPTIONS -v tc.lhs.top:15 #-}
-- {-# OPTIONS -v term:20 #-}

-- Andreas, 2014-11-08, following a complaint by Francesco Mazzoli

open import Common.Prelude

data Subst : (d : Nat) → Set where
  c₁ : ∀ {d}   → Subst d             → Subst d
  c₂ : ∀ d₁ d₂ → Subst d₁ → Subst d₂ → Subst (suc d₁ + d₂)

postulate
  comp : ∀ {d₁ d₂} → Subst d₁ → Subst d₂ → Subst (d₁ + d₂)

lookup : ∀ d → Nat → Subst d → Set₁
lookup d             zero    (c₁ ρ)        = Set
lookup d             (suc v) (c₁ ρ)        = lookup d v ρ
lookup .(suc d₁ + d₂) v       (c₂ d₁ d₂ ρ σ) = lookup (d₁ + d₂) v (comp ρ σ)

-- The dot pattern here is actually normalized, so it is
--
--   suc (d₁ + d₂)
--
-- the recursive call it with (d₁ + d₂).
-- In such simple cases, Agda can now recognize that the pattern is
-- constructor applied to call argument, which is valid descent.

-- This should termination check now.

-- Note however, that Agda only looks for syntactic equality,
-- since it is not allowed to normalize terms on the rhs (yet).

hidden : ∀{d} → Nat → Subst d → Set₁
hidden zero    (c₁ ρ)        = Set
hidden (suc v) (c₁ ρ)        = hidden v ρ
hidden v       (c₂ d₁ d₂ ρ σ) = hidden v (comp ρ σ)

-- This should also termination check, and looks pretty magical... ;-)

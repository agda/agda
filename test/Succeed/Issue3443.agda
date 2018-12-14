-- Issue reported by Sergei Meshvelliani
-- Simplified example by Guillaume Allais

-- When adding missing absurd clauses, dot patterns were accidentally
-- turned into variable patterns.

{-# OPTIONS --allow-unsolved-metas #-}

open import Agda.Builtin.List

open import Agda.Builtin.Equality

data Var (T : Set₂) (σ : T) : List T → Set₂ where
  z : ∀ Γ → Var T σ (σ ∷ Γ)
  s : ∀ τ Γ → Var T σ Γ → Var T σ (τ ∷ Γ)

eq : ∀ Γ (b c : Var _ Set Γ) → b ≡ c → Set
eq .(Set ∷ Γ) (z Γ) (z .Γ) _ = {!!}
eq .(τ ∷ Γ) (s τ Γ m) (s .τ .Γ n) _ = {!!}

-- WAS: Internal error in CompiledClause.Compile
-- SHOULD: Succeed

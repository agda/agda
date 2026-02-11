{-# OPTIONS --rewriting #-}

open import Agda.Builtin.Nat
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite
open import Agda.Builtin.Sigma

module LocalRewriteEtaMatch where

module Foo (z : Σ Nat (λ _ → Nat))
           (x y : Nat)
           (@rew p : z .fst ≡ x) where
  test : ∀ {z₁ z₂ z₃} → z₁ ≡ z₃ → z ≡ (z₁ , z₂) → x ≡ z₃
  test q refl = q

module Bar (z : Σ Nat (λ _ → Nat))
           (x y : Nat)
           (@rew p : x ≡ z .fst) where
  test : ∀ {z₁ z₂ z₃} → z₁ ≡ z₃ → z ≡ (z₁ , z₂) → x ≡ z₃
  test q refl = q

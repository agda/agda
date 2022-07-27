-- Andreas Abel, 2022-06-06, issue #5944 reported by Mike Shulman
-- Support rewriting with 2ltt (match SSet).

{-# OPTIONS --type-in-type --rewriting --two-level #-}

open import Agda.Primitive public

postulate
  Tel   : SSet
  ε     : Tel
  _≡_   : {A : SSet} (a : A) → A → SSet
  cong  : (A B : SSet) (f : A → B) {x y : A} (p : x ≡ y) → f x ≡ f y
  coe←  : (A B : SSet) → (A ≡ B) → B → A
  el    : Tel → SSet
  []    : el ε
  ID    : (Δ : Tel) → Tel
  ID′   : (Δ : Tel) (Θ : el Δ → Tel) → Tel
  ID′ε  : (Δ : Tel) → ID′ Δ (λ _ → ε) ≡ ε

{-# BUILTIN REWRITE _≡_ #-}
{-# REWRITE ID′ε #-}

postulate
  ID′-CONST   : (Θ : Tel) (Δ : Tel)

              → ID′ Θ (λ _ → Δ) ≡ ID Δ

  ID′-CONST-ε : (Θ : Tel) (δ₂ : el (ID ε))

              → coe← (el (ID′ Θ (λ _ → ε))) (el (ID ε)) (cong Tel (SSet lzero) el (ID′-CONST Θ ε)) δ₂ ≡ []

{-# REWRITE ID′-CONST-ε #-}

-- WAS: internal error when trying to make a pattern from SSet

-- Should succeed now

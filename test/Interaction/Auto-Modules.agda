module Auto-Modules where

open import Auto.Prelude hiding (cong; trans)

module NonemptySet (X : Set) (x : X) where
 h0 : (P : X → Set) → (∀ x → P x) → Σ X P
 h0 = {!!}
 -- h0 = λ P z → Σ-i x (z x)

module WithRAA (RAA : ∀ A → ¬ (¬ A) → A) where
 h1 : ∀ A → A ∨ ¬ A
 h1 A = {!!}
 -- h1 A = RAA (A ∨ ¬ A) (λ z → z (∨-i₂ (λ z₁ → z (∨-i₁ z₁))))

 module B (A : Set) where
  h2 : A ∨ ¬ A
  h2 = {!!}
  -- h2 = RAA (A ∨ ¬ A) (λ z → z (∨-i₂ (λ z₁ → z (∨-i₁ z₁))))

module B (X : Set) (x y : X) (P : X → Set) where
 postulate p : P x → P y

 h3 : P x → P y
 h3 px = {!p!}
 -- h3 = p px

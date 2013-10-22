-- Andreas, 2013-10-21
-- Test case for CheckInternal extracted from The Agda standard library
-- Propositional (intensional) equality

module FunExt where

open import Common.Level
open import Common.Equality

Extensionality : (a b : Level) → Set _
Extensionality a b =
  {A : Set a} {B : A → Set b} {f g : (x : A) → B x} →
  (∀ x → f x ≡ g x) → f ≡ g

-- Functional extensionality implies a form of extensionality for
-- Π-types.

∀-extensionality :
  ∀ {a b} →
  Extensionality a (lsuc b) →
  {A : Set a} (B₁ B₂ : A → Set b) →
  (∀ x → B₁ x ≡ B₂ x) → (∀ x → B₁ x) ≡ (∀ x → B₂ x)
∀-extensionality ext B₁ B₂ B₁≡B₂ with ext B₁≡B₂
∀-extensionality ext B .B  B₁≡B₂ | refl = refl

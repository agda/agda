-- Andreas, 2026-05-06, issue #5305
-- Reported and test case by Nisse, 2021-04-06
-- Generalization failure with --no-syntactic-equality

{-# OPTIONS --no-syntactic-equality #-}

open import Agda.Builtin.Equality
open import Agda.Builtin.Sigma
open import Agda.Primitive

variable
  A B : Set
  f   : A → B

Is-equivalence : {A B : Set} → (A → B) → Set
Is-equivalence f = ∀ y → Σ (Σ _ λ x → f x ≡ y) λ p → ∀ q → p ≡ q

inverse : {f : A → B} → Is-equivalence f → B → A
inverse eq y = fst (fst (eq y))

right-inverse-of :
  (eq : Is-equivalence f) → ∀ x → f (inverse eq x) ≡ x
right-inverse-of eq x = snd (fst (eq x))

_ :
  (eq : Is-equivalence f) →
  ∀ y (p : Σ _ λ x → f x ≡ y) →
  (inverse eq y , right-inverse-of eq y) ≡ p
_ = λ eq y → snd (eq y)

-- WAS: unsolved metas

-- Should succeed

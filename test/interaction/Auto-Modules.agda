module Auto-Modules where

open import Auto.Prelude hiding (cong; trans)


module NonemptySet (X : Set) (x : X) where
 h0 : (P : X → Set) → (∀ x → P x) → Σ X P
 h0 = {!!}
-- h0 = λ P h → Σ-i x (h x)

module WithRAA (RAA : ∀ A → ¬ (¬ A) → A) where
 h1 : ∀ A → A ∨ ¬ A
 h1 = {!!}
 --h1 = λ A → RAA (A ∨ ((x : A) → ⊥)) (λ z → z (∨-i₂ (λ x → z (∨-i₁ x))))

 module B where
  h2 : ∀ A → A ∨ ¬ A
  h2 = {!!}

module A (X : Set) (x : X) where
 postulate AllSame : {x y : X} → x ≡ y

 n0 : (P : X → Set) → Σ X P → ∀ x → P x
-- n0 = {!subst AllSame!}  -- no solution found
 n0 = λ P h x → subst P (Σ.wit h) x AllSame (Σ.prf h)

module B (X : Set) (x y : X) (P : X → Set) where
 postulate p : P x

 h3 : P x
 h3 = {!p!}
-- h3 = p



module Setoid (X : Set)
              (Eq : X → X → Set)
              (refl : ∀ {x} → Eq x x)
              (symm : ∀ {x₁ x₂} → Eq x₁ x₂ → Eq x₂ x₁)
              (subst : ∀ {x₁ x₂} → (P : X → Set) → Eq x₁ x₂ → P x₁ → P x₂)
 where
 cong : ∀ {x₁ x₂} → (f : X → X) → Eq x₁ x₂ → Eq (f x₁) (f x₂)
 cong = {!!}  -- hole 4
-- cong = λ {x₁} {x₂} f z → subst (λ z₁ → Eq (f x₁) (f z₁)) z refl

 trans : ∀ {x₁ x₂ x₃} → Eq x₁ x₂ → Eq x₂ x₃ → Eq x₁ x₃
 trans = {!!}  -- hole 5
-- trans = λ {x₁} {x₂} {x₃} z z₁ → subst (Eq x₁) z₁ z


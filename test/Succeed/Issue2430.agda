-- Andreas, 2017-01-24, issue #2430, reported by nad

-- Regression introduced by updating module parameter substitution
-- when going underAbstraction (80794767db1aceaa78a72e06ad901cfa53f8346d).

record Σ (A : Set) (B : A → Set) : Set where
  field
    proj₁ : A
    proj₂ : B proj₁

open Σ public

Σ-map : {A : Set} {B : Set} {P : A → Set} {Q : B → Set} →
        (f : A → B) → (∀ {x} → P x → Q (f x)) →
        Σ A P → Σ B Q
Σ-map f g p = record { proj₁ = f (proj₁ p); proj₂ = g (proj₂ p) }

postulate

  _≡_        : {A : Set} → A → A → Set
  refl       : {A : Set} (x : A) → x ≡ x
  cong       : {A : Set} {B : Set} (f : A → B) {x y : A} →
               x ≡ y → f x ≡ f y
  cong-refl  : {A : Set} {B : Set} (f : A → B) {x : A} →
               refl (f x) ≡ cong f (refl x)
  subst      : {A : Set} (P : A → Set) {x y : A} →
               x ≡ y → P x → P y
  subst-refl : ∀ {A : Set} (P : A → Set) {x} (p : P x) →
               subst P (refl x) p ≡ p
  trans      : {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z

module _ (_ : Set) where

  postulate

    Σ-≡,≡→≡ : {A : Set} {B : A → Set} {p₁ p₂ : Σ A B} →
              (p : proj₁ p₁ ≡ proj₁ p₂) →
              subst B p (proj₂ p₁) ≡ proj₂ p₂ →
              p₁ ≡ p₂

    Σ-≡,≡→≡-refl-subst-refl :
      ∀ {A : Set} {B : A → Set} {p} →
      Σ-≡,≡→≡ (refl (proj₁ p)) (subst-refl B (proj₂ p)) ≡ refl p

  rejected :
    {A₁ A₂ : Set} {B₁ : A₁ → Set} {B₂ : A₂ → Set}
    (f : A₁ → A₂) (g : ∀ x → B₁ x → B₂ (f x)) (x : Σ A₁ B₁) →
    Σ-≡,≡→≡ (refl _) (subst-refl B₂ _) ≡ cong (Σ-map f (g _)) (refl x)
  rejected {B₁ = B₁} {B₂} f g x =
    trans {x = Σ-≡,≡→≡ (refl _) (subst-refl B₂ _)}
          {z = cong (Σ-map f (g _)) (refl _)}
          Σ-≡,≡→≡-refl-subst-refl
          (cong-refl _)

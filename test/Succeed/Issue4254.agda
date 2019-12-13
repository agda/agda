
open import Agda.Builtin.Equality
open import Agda.Builtin.Nat

data D (A : Set) : Set → Set₁ where
  c₁ : {B : Set} → D A B
  c₂ : D A A

record P {A B : Set} (p : D A B) : Set₁ where
  constructor c
  field
    d : D A B

Q : {A B₁ B₂ C : Set} {x : D A (B₁ → C)} {y : D A B₂} →
    P x → P y → B₁ ≡ B₂ → Nat
Q (c c₁) _      refl = 0
Q _      (c c₁) refl = 1
Q _      _      _    = 2

module _ {A B C : Set} where

  checkQ₀ : {x : D A (B → C)} {y : D A B} (px : P x) (py : P y) →
              Q {x = x} {y = y} (c c₁) py refl ≡ 0
  checkQ₀ _ _ = refl

  checkQ₁ : {x : D (A → B) (A → B)} {y : D (A → B) A} (px : P x) (py : P y) →
              Q {x = x} {y = y} (c c₂) (c c₁) refl ≡ 1
  checkQ₁ _ _ = refl

  checkQ₂ : {x : D (A → B) (A → B)} {y : D (A → B) (A → B)} (px : P x) (py : P y) (eq : A ≡ (A → B)) →
              Q {x = x} {y = y} (c c₂) (c c₂) eq ≡ 2
  checkQ₂ _ _ _ = refl

R : {A B₁ B₂ C : Set} {x : D A (B₁ → C)} {y : D A B₂} →
    P x → P y → B₁ ≡ B₂ → Nat
R (c c₂) _      refl = 0
R _      (c c₂) refl = 1
R _      _      _    = 2

module _ {A B C : Set} where

  checkR₀ : ∀ {B C} {x : D (B → C) (B → C)} {y : D (B → C) B} (px : P x) (py : P y) →
             R {x = x} {y = y} (c c₂) py refl ≡ 0
  checkR₀ _ _ = refl

  checkR₁ : ∀ {A B} {x : D A (A → B)} {y : D A A} (px : P x) (py : P y) →
             R {x = x} {y = y} (c c₁) (c c₂) refl ≡ 1
  checkR₁ _ _ = refl

  checkR₂ : ∀ {A B C} {x : D A (B → C)} {y : D A B} (px : P x) (py : P y) →
             R {x = x} {y = y} (c c₁) (c c₁) refl ≡ 2
  checkR₂ _ _ = refl

{-# OPTIONS --erasure #-}

record R₁ : Set₂ where
  field
    _≡_ : {A : Set₁} → A → A → Set

postulate
  A B : Set

record R₂ (r₁ : R₁) : Set₂ where
  open R₁ r₁
  field
    cong  : (A : Set₁) (x y : A) (F : A → Set) → x ≡ y → F x ≡ F y
    subst : (P : Set → Set₁) → A ≡ B → P A → P B

postulate
  _≡_ : {A : Set₁} → A → A → Set

r₁ : R₁
r₁ .R₁._≡_ = _≡_

postulate
  r₂ : ∀ r₁ → R₂ r₁

open R₂ (r₂ r₁)

record R₃ (@0 A : Set₁) : Set₁ where
  constructor [_]
  field
    f : A

postulate
  r₃            : R₃ Set
  push-subst-[] :
    (P : Set → Set₁) (p : P A) (eq : A ≡ B) →
    subst (λ A → R₃ (P A)) eq [ p ] ≡ [ subst P eq p ]

_ :
  (eq : A ≡ B) →
  (subst (λ _ → R₃ Set) eq r₃ ≡ r₃) ≡
  ([ subst (λ _ → Set) eq (r₃ .R₃.f) ] ≡ r₃)
_ = λ eq → cong _ _ _ (_≡ _) (push-subst-[] _ _ _)

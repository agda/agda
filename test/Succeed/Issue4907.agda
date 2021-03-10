
_∘_ : {A : Set} {B : A → Set} {C : {x : A} → B x → Set₁} →
      (∀ {x} (y : B x) → C y) → (g : (x : A) → B x) →
      ((x : A) → C (g x))
f ∘ g = λ x → f (g x)

postulate
  R : {A : Set₁} → A → A → Set₁

_≡_ : {A : Set₁} → A → A → Set₁
_≡_ = R

data D (A : Set) : Set where
  c : A → D A

postulate
  cong  : {A B : Set₁} {x y : A} (f : A → B) → x ≡ y → f x ≡ f y
  refl  : {A : Set₁} {x : A} → x ≡ x
  A     : Set
  P     : D A → Set
  p     : (F : A → Set) → (P ∘ c) ≡ F → (P ∘ c) ≡ F
  eq    : P ≡ P

_ : p (P ∘ c) (cong (_∘ c) eq) ≡ p (P ∘ c) (cong (_∘ c) eq)
_ = cong (λ eq → p _ eq) (cong (cong (_∘ c)) refl)

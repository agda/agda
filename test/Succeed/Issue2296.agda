
record R₁ (M : Set → Set) : Set₁ where
  field
    return : ∀ {A} → A → M A
    map    : ∀ {A B} → (A → B) → M A → M B

open R₁ ⦃ … ⦄ public

record R₂ (M : Set → Set) : Set₁ where
  field
    instance
      r₁ : R₁ M

data Wrap₁ (A : Set) : Set where
  box : A → Wrap₁ A

instance

  r₁ : R₁ Wrap₁
  R₁.return r₁ x         = box x
  R₁.map    r₁ f (box x) = box (f x)

record Wrap₂ (A : Set) : Set where
  field
    run : A

postulate
  instance
    r₂ : R₂ Wrap₂

  A     : Set
  f     : A → A
  g     : A → Wrap₁ A
  _≡_   : {A : Set} → A → A → Set
  refl  : {A : Set} (x : A) → x ≡ x
  trans : {A : Set} (x : A) {y z : A} → x ≡ y → y ≡ z → x ≡ z
  id    : {A : Set} (x : A) {y : A} → x ≡ y → x ≡ y

h : ∀ x → map f (g x) ≡ map f (return x) → map f (g x) ≡ return (f x)
h x eq =
  trans (map f (g x))
    eq
    (id (map f (return x))
        (refl (return (f x))))

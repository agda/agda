
data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x

record R₁ (F : Set → Set) : Set₁ where
  constructor mkR₁
  field
    f₁ : ∀ {A} → A → F A

open R₁ {{...}}

record R₂ (F : Set → Set) : Set₁ where
  constructor mkR₂
  field
    instance
      r₁ : R₁ F

open R₂ {{...}}

record R₃ (_ : Set) : Set where
  constructor mkR₃

postulate
  instance
    r₃ : R₂ R₃

  A : Set
  a : A

record R₄ : Set where
  constructor c
  field
    f₂ : A

postulate
  F : (r₄ : R₄) → c a ≡ r₄ → Set

G : Set → Set
G _ = F _ (refl {x = f₁ a})

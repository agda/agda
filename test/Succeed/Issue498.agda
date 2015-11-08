-- Issue498: Underapplied projection-like functions did not evaluate correctly.
module Issue498 where

data ⊤ : Set where
  tt : ⊤

data C : ⊤ → Set where
  c : C tt

data C₂ : ⊤ → ⊤ → Set where
  c : C₂ tt tt

module NoParams where

  f₁ : ∀ a → C a → ⊤
  f₁ a x = tt

  f₁′ : ∀ a → C a → ⊤
  f₁′ = f₁

  check₁ : ∀ a x → C (f₁′ a x)
  check₁ s x = c

  f₂ : ∀ a b → C₂ a b → ⊤
  f₂ a b x = tt

  f₂′ : ∀ a b → C₂ a b → ⊤
  f₂′ a = f₂ a

  check₂ : ∀ a b x → C (f₂′ a b x)
  check₂ a b x = c

  f₃ : ∀ a {b} → C₂ a b → ⊤
  f₃ a x = tt

  f₃′ : ∀ a {b} → C₂ a b → ⊤
  f₃′ = f₃

  data Is-f₃ : (∀ a {b} → C₂ a b → ⊤) → Set where
    is-f₃ : Is-f₃ (λ a {b} x → tt)

  check₃ : Is-f₃ f₃′
  check₃ = is-f₃

module SomeParams (X Y : Set) where

  f₁ : ∀ a → C a → ⊤
  f₁ a x = tt

  f₁′ : ∀ a → C a → ⊤
  f₁′ = f₁

  check₁ : ∀ a x → C (f₁′ a x)
  check₁ s x = c

  f₂ : ∀ a b → C₂ a b → ⊤
  f₂ a b x = tt

  f₂′ : ∀ a b → C₂ a b → ⊤
  f₂′ a = f₂ a

  check₂ : ∀ a b x → C (f₂′ a b x)
  check₂ a b x = c

check₃ : ∀ {X Y} a x → C (SomeParams.f₁′ X Y a x)
check₃ a x = c

check₄ : ∀ {X Y} a b x → C (SomeParams.f₂′ X Y a b x)
check₄ a b x = c

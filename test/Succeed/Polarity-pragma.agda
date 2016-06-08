data ⊥ : Set where

module M₁ where

  postulate
    ∥_∥ : Set → Set

  {-# POLARITY ∥_∥ ++ #-}

  data D : Set where
    c : ∥ D ∥ → D

module M₂ where

  postulate
    _⇒_    : Set → Set → Set
    lambda : {A B : Set} → (A → B) → A ⇒ B
    apply  : {A B : Set} → A ⇒ B → A → B

  {-# POLARITY _⇒_ ++ #-}

  data D : Set where
    c : D ⇒ ⊥ → D

  not-inhabited : D → ⊥
  not-inhabited (c f) = apply f (c f)

  d : D
  d = c (lambda not-inhabited)

  bad : ⊥
  bad = not-inhabited d

postulate
  F₁ : Set → Set → Set₁ → Set₁ → Set₁ → Set

{-# POLARITY F₁ _ ++ + - * #-}

data D₁ : Set where
  c : F₁ (D₁ → ⊥) D₁ Set Set Set → D₁

postulate
  F₂ : ∀ {a} → Set a → Set a → Set a

{-# POLARITY F₂ * * ++ #-}

data D₂ (A : Set) : Set where
  c : F₂ A (D₂ A) → D₂ A

module _ (A : Set₁) where

  postulate
    F₃ : Set → Set

  {-# POLARITY F₃ ++ #-}

data D₃ : Set where
  c : F₃ Set D₃ → D₃

postulate
  F₄ : ∀ {a} → Set a → Set a → Set a

{-# POLARITY F₄ * ++ #-}

data D₄ (A : Set) : Set where
  c : F₄ (D₄ A) A → D₄ A

postulate
  F₅ : ⦃ _ : Set ⦄ → Set

{-# POLARITY F₅ ++ #-}

data D₅ : Set where
  c : F₅ ⦃ D₅ ⦄ → D₅

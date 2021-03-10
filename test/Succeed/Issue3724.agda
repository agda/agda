{-# OPTIONS --prop --allow-unsolved-metas #-}

data _≡_ {α}{A : Set α}(a : A) : A → Prop where
  refl : a ≡ a

data _≃_ {α}{A : Set α}(a : A) : ∀ {B} → B → Prop where
  refl̃ : a ≃ a

data ⊥ : Set where

data Con  : Set
data Con~ : Con → Con → Prop
data Ty   : Con → Set
data Ty~  : ∀ {Γ₀ Γ₁} → Con~ Γ₀ Γ₁ → Ty Γ₀ → Ty Γ₁ → Prop

data Con where
data Con~ where

data Ty where
  U  : ∀ {Γ} → Ty Γ

data Ty~ where
  U~  : ∀ {Γ₀ Γ₁ Γ₀₁} → Ty~ {Γ₀}{Γ₁} Γ₀₁ U U

Conᴹ  : Con → Set
Con~ᴹ : ∀ {Γ₀ Γ₁} → Con~ Γ₀ Γ₁ → Conᴹ Γ₀ ≡ Conᴹ Γ₁
Tyᴹ   : ∀ {Γ} → Ty Γ → Conᴹ Γ → Set
Ty~ᴹ  : ∀ {Γ₀ Γ₁ Γ₀₁ A₀ A₁} → Ty~ {Γ₀}{Γ₁} Γ₀₁ A₀ A₁ → Tyᴹ A₀ ≃ Tyᴹ A₁
Conᴹ  ()
Con~ᴹ ()

Tyᴹ U γ = ⊥

-- offending line: if I comment this out, the internal error goes away
-- If I use Set instead of Prop everywhere, the error also goes away
Ty~ᴹ U~ = {!!}

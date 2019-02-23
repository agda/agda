
open import Agda.Builtin.Equality

data D (A : Set) : Set where

{-# INJECTIVE D #-}

test : {A₁ A₂ : Set} → D A₁ ≡ D A₂ → A₁ ≡ A₂
test refl = refl

postulate f : Set → Set

{-# INJECTIVE f #-}

f' = f

test₂ : {A₁ A₂ : Set} → f A₁ ≡ f' A₂ → A₁ ≡ A₂
test₂ refl = refl

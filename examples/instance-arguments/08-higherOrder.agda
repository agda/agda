module 08-higherOrder where

explicitize : ∀ {A : Set} {B : A → Set} → ({{x : A}} → B x) → (x : A) → B x
explicitize f x = f {{x}}

implicitize : ∀ {A : Set} {B : A → Set} → ((x : A) → B x) → {{x : A}} → B x
implicitize f {{x}} = f x

data T : Set where
  tt : T

test = explicitize (λ {{t : T}} → t)

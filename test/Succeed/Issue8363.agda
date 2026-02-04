module Issue8363 where

postulate
  A : Set
  P : {B : Set} → B → Set
  p : {B C : Set} {x : B} (f : B → C) → P (f x)

record R (F : Set → Set) : Set₁ where
  field
    r₁ : A → F A
    r₂ : F A → (A → F A) → F A

open R ⦃ … ⦄

_ : {F : Set → Set} ⦃ r : R F ⦄ (x : F A) → P (r₂ x r₁)
_ = λ x → p (λ h → r₂ x h)

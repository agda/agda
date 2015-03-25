
postulate
  P : {A : Set} → A → A → Set
  p : {A : Set} {x : A} → P x x
  q : {A : Set} (x : A) {y : A} → P x y → P x y
  A : Set

record R (F : Set → Set) : Set₁ where
  field
    f₁ : (A → A) → F A → F A
    f₂ : P (f₁ (λ x → x)) (λ (x : F A) → x)

open R ⦃ … ⦄ public

instance

  r : R (λ O → O → O)
  r = record
    { f₁ = λ f g x → f (g x)
    ; f₂ = p
    }

postulate
  F : Set → Set

  instance
    rF : R F

Foo : P (f₁ (λ x → x)) (λ (x : F A) → x)
Foo = q (f₁ (λ x → x)) f₂

-- An internal error has occurred. Please report this as a bug.
-- Location of the error:
-- src/full/Agda/TypeChecking/InstanceArguments.hs:224

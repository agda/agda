
open import Agda.Primitive

_∘_ : ∀ {a b c}
        {A : Set a} {B : A → Set b} {C : {x : A} → B x → Set c} →
      (∀ {x} (y : B x) → C y) → (g : (x : A) → B x) →
      ((x : A) → C (g x))
f ∘ g = λ x → f (g x)

data D {a} (A : Set a) : Set a where
  d : D A → D A

data E {a} (A : Set a) : Set a where
  e : A → E A

F : ∀ {a} {A : Set a} → A → D A → Set a
F x (d ys) = E (F x ys)

G : ∀ {a} {A : Set a} → D A → D A → Set a
G xs ys = ∀ x → F x xs → F x ys

postulate
  H : ∀ {a} {A : Set a} {xs ys : D A} → G xs ys → Set

variable
  a  : Level
  A  : Set a
  P  : A → Set a
  x  : A
  xs : D A

postulate
  h : {f : G xs xs} (_ : P x) → F x xs → H (λ _ → e ∘ f _)

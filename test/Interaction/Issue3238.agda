open import Agda.Builtin.Equality

_∘_ : ∀ {a b c}
        {A : Set a} {B : A → Set b} {C : {x : A} → B x → Set c} →
        (f : ∀ {x} (y : B x) → C y) →
        (g : (x : A) → B x) →
        ((x : A) → C (g x))
f ∘ g = λ x → f (g x)

postulate
  A : Set
  B : A → Set
  C : {x : A} → B x → Set
  f : ∀ {x : A} (y : B x) → C y
  g : (x : A) → B x

test : (f ∘ g) ≡ (f ∘ g)
test = {!!}

-- WAS: goal displayed as ((λ {x} -> f) ∘ g) ≡ ((λ {x} -> f) ∘ g)
-- WANT: no spurious hidden lambda i.e. (f ∘ g) ≡ (f ∘ g)

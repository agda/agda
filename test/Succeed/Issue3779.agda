open import Agda.Builtin.Equality

variable
  A B : Set
  f g : A

postulate
  F   : Set → Set
  map : (A → B) → F A → F B

lemma : (x : F A) → map (λ x → f (g x)) x ≡ map f (map g x) → F A
lemma {A = A} {f = f} {g = g} x _ = x

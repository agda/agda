apply :
  ∀ {a b} {A : Set a} {B : A → Set b} →
  ((x : A) → B x) → (x : A) → B x
apply f x = f x

syntax apply f x = f x

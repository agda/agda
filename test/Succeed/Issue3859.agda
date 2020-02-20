{-# OPTIONS --allow-unsolved-metas #-}

open import Agda.Builtin.Equality

postulate
  cong₂ : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c} {x y : A} {u v : B}
        → (f : A → B → C) → x ≡ y → u ≡ v → f x u ≡ f y v

test = cong₂ (λ A B → A → B)

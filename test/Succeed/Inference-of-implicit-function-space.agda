module Inference-of-implicit-function-space where

postulate
  _⇔_         : Set → Set → Set
  equivalence : {A B : Set} → (A → B) → (B → A) → A ⇔ B
  A           : Set

P : Set
P = {x : A} → A ⇔ A

works : P ⇔ P
works = equivalence (λ r {x} → r {x = x}) (λ r {x} → r {x = x})

works₂ : P ⇔ P
works₂ = equivalence {A = P} (λ r {x} → r {x = x}) (λ r {y} → r {y})

fails : P ⇔ P
fails = equivalence (λ r {x} → r {x = x}) (λ r {y} → r {y})

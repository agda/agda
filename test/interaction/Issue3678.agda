open import Agda.Builtin.Sigma
open import Agda.Builtin.Equality

postulate
  A : Set
  B : A → Set
  a : A

Pi : (A → Set) → Set
Pi B = {x : A} → B x

foo : Pi \ y →  Σ (B y) \ _ → Pi \ z → Σ (y ≡ a → B z) \ _ → B y → B z → A
foo = {!!} , (\ { refl → {!!} }) , {!!}

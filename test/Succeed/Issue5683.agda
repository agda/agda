
open import Agda.Builtin.Equality
open import Agda.Builtin.Sigma

postulate X : Set
variable x : X

data C : Σ X (λ x → x ≡ x) → Set where
  mkC :
    let
      eq : x ≡ x  -- don't generalize over x at eq
      eq = refl {x = x}
    in
    C (x , eq)


open import Agda.Builtin.Sigma

dup : ∀ {A : Set} → A → Σ A λ _ → A
dup x = x , x

postulate
  A : Set

module M {x : A} where
  y = x

data X : Set where
  mkX : ∀ {x : A}
    → let
        (_ , _) = dup x
        open M {x}
      in
      X

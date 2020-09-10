
-- By Philipp Hausmann.

open import Agda.Builtin.Bool
open import Agda.Builtin.Equality
open import Agda.Builtin.Float

data ⊥ : Set where

_/_ = primFloatDiv
_<_ = primFloatLess

cong : {A B : Set} {x y : A} (f : A → B) → x ≡ y → f x ≡ f y
cong f refl = refl

0eq : 0.0 ≡ -0.0
0eq = refl

bug : ⊥
bug = f (cong (λ x → (1.0 / x) < 0.0) 0eq)
  where
    f : false ≡ true → ⊥
    f ()

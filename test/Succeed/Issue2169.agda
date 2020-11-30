
open import Agda.Builtin.Bool
open import Agda.Builtin.Equality
open import Agda.Builtin.Float

data ⊥ : Set where

defNegZero : -0.0 ≡ 0.0 → ⊥
defNegZero ()

primEqNegZero : primFloatEquality -0.0 0.0 ≡ true
primEqNegZero = refl

primLtNegZero₁ : primFloatLess 0.0 -0.0 ≡ false
primLtNegZero₁ = refl

primLtNegZero₂ : primFloatLess -0.0 0.0 ≡ false
primLtNegZero₂ = refl

primShowNegZero : primShowFloat -0.0 ≡ "-0.0"
primShowNegZero = refl

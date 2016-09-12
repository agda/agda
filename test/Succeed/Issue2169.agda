
open import Agda.Builtin.Bool
open import Agda.Builtin.Equality
open import Agda.Builtin.Float

data ⊥ : Set where

NaN : Float
NaN = primFloatDiv 0.0 0.0

defNegZero : -0.0 ≡ 0.0 → ⊥
defNegZero ()

primEqNegZero : primFloatEquality -0.0 0.0 ≡ false
primEqNegZero = refl

-- TODO
-- primLtNegZero : primFloatLess -0.0 0.0 ≡ true
-- primLtNegZero = refl

primShowNegZero : primShowFloat -0.0 ≡ "-0.0"
primShowNegZero = refl

defNaN : NaN ≡ NaN
defNaN = refl

primEqNaN : primFloatEquality NaN NaN ≡ true
primEqNaN = refl

-- TODO
-- primLtNaN : primFloatLess NaN NaN ≡ false
-- primLtNaN = refl

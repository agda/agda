
open import Agda.Builtin.Bool
open import Agda.Builtin.Equality
open import Agda.Builtin.Float

NaN : Float
NaN = primFloatDiv 0.0 0.0

defNaN : NaN ≡ NaN
defNaN = refl

primEqNaN : primFloatEquality NaN NaN ≡ false
primEqNaN = refl

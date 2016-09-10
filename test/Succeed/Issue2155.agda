
open import Common.Equality
open import Common.Prelude

NaN : Float
NaN = primFloatDiv 0.0 0.0

ok : primFloatEquality NaN NaN ≡ true
ok = refl

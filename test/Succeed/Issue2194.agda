
open import Common.Equality
open import Common.Prelude

NaN : Float
NaN = primFloatDiv 0.0 0.0

NaN≢-NaN : primFloatEquality NaN (primFloatNegate NaN) ≡ true
NaN≢-NaN = refl

NaN≢N-NaN : primFloatNumericalEquality NaN (primFloatNegate NaN) ≡ false
NaN≢N-NaN = refl

module FloatToRatio where

open import Agda.Builtin.Equality
open import Agda.Builtin.Float
open import Agda.Builtin.Int
open import Agda.Builtin.Sigma

NaN Infinity -Infinity : Float
NaN = primFloatDiv 0.0 0.0
Infinity = primFloatDiv 1.0 0.0
-Infinity = primFloatDiv -1.0 0.0

_ : primFloatToRatio 1.5 ≡ (pos 3 , 2)
_ = refl

_ : primFloatToRatio NaN ≡ (pos 0 , 0)
_ = refl

_ : primFloatToRatio Infinity ≡ (pos 1 , 0)
_ = refl

_ : primFloatToRatio -Infinity ≡ (negsuc 0 , 0)
_ = refl

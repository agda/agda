open import Agda.Builtin.Bool
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Float
  renaming ( primFloatEquality to _≡ᵇ_
           ; primFloatDiv      to _÷_
           ; primFloatNegate   to -_
           ; primShowFloat     to show
           ; primFloatToRatio  to toRatio
           ; primRatioToFloat  to fromRatio
           ; primFloatDecode   to decode
           ; primFloatEncode   to encode
           )
open import Agda.Builtin.Int
open import Agda.Builtin.Maybe
open import Agda.Builtin.Sigma

-- Prelude

data ⊥ : Set where

_≢_ : {A : Set} (P Q : A) → Set
P ≢ Q = P ≡ Q → ⊥

NaN : Float
NaN = 0.0 ÷ 0.0

Infinity : Float
Infinity = 1.0 ÷ 0.0

-Infinity : Float
-Infinity = -1.0 ÷ 0.0


-- * Tests

-- ** Corner cases

_ : NaN ≡ - NaN
_ = refl

_ : -0.0 ≢ 0.0
_ = λ ()

_ : Infinity ≢ -Infinity
_ = λ ()

_ : Infinity ≡ Infinity
_ = refl

_ : -Infinity ≡ -Infinity
_ = refl

_ : Infinity ≡ - -Infinity
_ = refl

_ : Infinity ≢ -Infinity
_ = λ ()

_ : show NaN ≡ "NaN"
_ = refl

_ : show (- NaN) ≡ "NaN"
_ = refl

_ : NaN ≡ᵇ NaN ≡ false
_ = refl

_ : show -0.0 ≡ "-0.0"
_ = refl

_ : show 0.0 ≡ "0.0"
_ = refl

_ : show 1.0 ≡ "1.0"
_ = refl


-- Decoding and Encoding

_ : decode NaN ≡ nothing
_ = refl

_ : decode Infinity ≡ nothing
_ = refl

_ : decode -Infinity ≡ nothing
_ = refl

_ : decode 1.5 ≡ just (pos 3 , negsuc 0)
_ = refl

_ : encode (pos 3) (negsuc 0) ≡ 1.5
_ = refl


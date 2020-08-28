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

-NaN : Float
-NaN = - NaN

Infinity : Float
Infinity = 1.0 ÷ 0.0

-Infinity : Float
-Infinity = - Infinity


-- * Tests

-- ** Corner cases

_ : -NaN      ≡    NaN      ; _ = refl
_ : -0.0      ≢    0.0      ; _ = λ ()
_ :  Infinity ≢   -Infinity ; _ = λ ()
_ :  Infinity ≡    Infinity ; _ = refl
_ : -Infinity ≡   -Infinity ; _ = refl
_ :  Infinity ≡ - -Infinity ; _ = refl
_ :  Infinity ≢   -Infinity ; _ = λ ()

_ : show  NaN      ≡  "NaN"      ; _ = refl
_ : show -NaN      ≡  "NaN"      ; _ = refl
_ : show  0.0      ≡  "0.0"      ; _ = refl
_ : show -0.0      ≡ "-0.0"      ; _ = refl
_ : show  Infinity ≡  "Infinity" ; _ = refl
_ : show -Infinity ≡ "-Infinity" ; _ = refl
_ : show  1.0      ≡  "1.0"      ; _ = refl
_ : show  1.5      ≡  "1.5"      ; _ = refl

_ :  NaN      ≡ᵇ  NaN      ≡ false ; _ = refl
_ : -NaN      ≡ᵇ  NaN      ≡ false ; _ = refl
_ :  NaN      ≡ᵇ -NaN      ≡ false ; _ = refl
_ : -NaN      ≡ᵇ -NaN      ≡ false ; _ = refl
_ :  Infinity ≡ᵇ  Infinity ≡ true  ; _ = refl
_ : -Infinity ≡ᵇ  Infinity ≡ false ; _ = refl
_ :  Infinity ≡ᵇ -Infinity ≡ false ; _ = refl
_ : -Infinity ≡ᵇ -Infinity ≡ true  ; _ = refl


-- ** Decoding and Encoding

_ : decode  NaN                                  ≡ nothing                      ; _ = refl
_ : decode  Infinity                             ≡ nothing                      ; _ = refl
_ : decode -Infinity                             ≡ nothing                      ; _ = refl
_ : decode  1.0                                  ≡ just (pos 1 , pos 0)         ; _ = refl
_ : decode  1.5                                  ≡ just (pos 3 , negsuc 0)      ; _ = refl

_ : encode  (pos 1) (pos 0)                      ≡ just 1.0                     ; _ = refl
_ : encode  (pos 3) (negsuc 0)                   ≡ just 1.5                     ; _ = refl
_ : encode  (pos 9007199254740991) (pos 0)       ≡ just 9007199254740991.0      ; _ = refl
_ : encode  (pos 9007199254740991) (pos 971)     ≡ just 1.7976931348623157e308  ; _ = refl
_ : encode  (pos 9007199254740991) (negsuc 1023) ≡ just 5.0104209000224314e-293 ; _ = refl

-- * Ratios

_ : toRatio  NaN      ≡ (pos 0    , pos 0) ; _ = refl
_ : toRatio  Infinity ≡ (pos 1    , pos 0) ; _ = refl
_ : toRatio -Infinity ≡ (negsuc 0 , pos 0) ; _ = refl
_ : toRatio  1.0      ≡ (pos 1    , pos 1) ; _ = refl
_ : toRatio  1.5      ≡ (pos 3    , pos 2) ; _ = refl


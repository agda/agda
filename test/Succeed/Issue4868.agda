open import Agda.Builtin.Bool
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Float
  renaming ( primFloatEquality       to _≡ᵇ_
           ; primFloatInequality     to _≤ᵇ_
           ; primFloatLess           to _<ᵇ_
           ; primFloatPlus           to infixl 6 _+_
           ; primFloatMinus          to infixl 6 _-_
           ; primFloatTimes          to infixl 7 _*_
           ; primFloatDiv            to infixl 7 _÷_
           ; primFloatPow            to infix  8 _**_
           ; primFloatNegate         to infix  9 -_
           ; primFloatSqrt           to sqrt
           ; primFloatExp            to e^_
           ; primFloatLog            to log
           ; primFloatSin            to sin
           ; primFloatCos            to cos
           ; primFloatTan            to tan
           ; primFloatASin           to asin
           ; primFloatACos           to acos
           ; primFloatATan           to atan
           ; primFloatATan2          to atan2
           ; primFloatSinh           to sinh
           ; primFloatCosh           to cosh
           ; primFloatTanh           to tanh
           ; primFloatASinh          to asinh
           ; primFloatACosh          to acosh
           ; primFloatATanh          to atanh
           ; primFloatRound          to round
           ; primFloatFloor          to floor
           ; primFloatCeiling        to ceiling
           ; primShowFloat           to show
           ; primFloatToWord64       to toWord
           ; primFloatToRatio        to toRatio
           ; primRatioToFloat        to fromRatio
           ; primFloatDecode         to decode
           ; primFloatEncode         to encode
           ; primFloatIsInfinite     to isInfinite
           ; primFloatIsNaN          to isNaN
           ; primFloatIsNegativeZero to isNegativeZero
           ; primFloatIsSafeInteger  to isSafeInteger
           )
open import Agda.Builtin.Int
open import Agda.Builtin.Maybe
open import Agda.Builtin.Sigma
open import Agda.Builtin.Word
  renaming ( primWord64ToNat to toℕ
           )

-- Prelude

data ⊥ : Set where

_≢_ : {A : Set} (P Q : A) → Set
P ≢ Q = P ≡ Q → ⊥

fmap : {A B : Set} → (A → B) → Maybe A → Maybe B
fmap f nothing  = nothing
fmap f (just x) = just (f x)

NaN : Float
NaN = 0.0 ÷ 0.0

-NaN : Float
-NaN = - NaN

Infinity : Float
Infinity = 1.0 ÷ 0.0

-Infinity : Float
-Infinity = - Infinity

MaxFloat : Float
MaxFloat = 1.7976931348623157e308

MinFloat : Float
MinFloat = 2.2250738585072014e-308

MaxSafeIntF : Float
MaxSafeIntF = 9007199254740991.0

MaxSafeIntZ : Int
MaxSafeIntZ = pos 9007199254740991

-- * Tests

-- ** Relations

_ : -NaN      ≡    NaN      ; _ = refl
_ : -0.0      ≢    0.0      ; _ = λ ()
_ :  Infinity ≢   -Infinity ; _ = λ ()
_ :  Infinity ≡    Infinity ; _ = refl
_ : -Infinity ≡   -Infinity ; _ = refl
_ :  Infinity ≡ - -Infinity ; _ = refl
_ :  Infinity ≢   -Infinity ; _ = λ ()

_ :  NaN      ≡ᵇ  NaN      ≡ false ; _ = refl
_ : -NaN      ≡ᵇ  NaN      ≡ false ; _ = refl
_ :  NaN      ≡ᵇ -NaN      ≡ false ; _ = refl
_ : -NaN      ≡ᵇ -NaN      ≡ false ; _ = refl
_ :  Infinity ≡ᵇ  Infinity ≡ true  ; _ = refl
_ : -Infinity ≡ᵇ  Infinity ≡ false ; _ = refl
_ :  Infinity ≡ᵇ -Infinity ≡ false ; _ = refl
_ : -Infinity ≡ᵇ -Infinity ≡ true  ; _ = refl
_ :  MaxFloat ≡ᵇ  MaxFloat ≡ true  ; _ = refl
_ :  MinFloat ≡ᵇ  MinFloat ≡ true  ; _ = refl
_ :  1.0      ≡ᵇ  1.5      ≡ false ; _ = refl
_ :  1.0      ≡ᵇ  1.0      ≡ true  ; _ = refl
_ :  1.5      ≡ᵇ  1.5      ≡ true  ; _ = refl

_ :  NaN      ≤ᵇ  NaN      ≡ false ; _ = refl
_ : -NaN      ≤ᵇ  NaN      ≡ false ; _ = refl
_ :  NaN      ≤ᵇ -NaN      ≡ false ; _ = refl
_ : -NaN      ≤ᵇ -NaN      ≡ false ; _ = refl
_ :  NaN      ≤ᵇ  5.0      ≡ false ; _ = refl
_ : -NaN      ≤ᵇ  5.0      ≡ false ; _ = refl
_ :  5.0      ≤ᵇ -NaN      ≡ false ; _ = refl
_ : -5.0      ≤ᵇ -NaN      ≡ false ; _ = refl
_ :  NaN      ≤ᵇ  Infinity ≡ false ; _ = refl
_ : -NaN      ≤ᵇ  Infinity ≡ false ; _ = refl
_ :  Infinity ≤ᵇ -NaN      ≡ false ; _ = refl
_ : -Infinity ≤ᵇ -NaN      ≡ false ; _ = refl
_ :  Infinity ≤ᵇ  Infinity ≡ true  ; _ = refl
_ : -Infinity ≤ᵇ  Infinity ≡ true  ; _ = refl
_ :  Infinity ≤ᵇ -Infinity ≡ false ; _ = refl
_ : -Infinity ≤ᵇ -Infinity ≡ true  ; _ = refl
_ :  MaxFloat ≤ᵇ  MaxFloat ≡ true  ; _ = refl
_ :  MinFloat ≤ᵇ  MinFloat ≡ true  ; _ = refl
_ :  1.0      ≤ᵇ  1.5      ≡ true  ; _ = refl
_ :  1.0      ≤ᵇ  1.0      ≡ true  ; _ = refl
_ :  1.5      ≤ᵇ  1.5      ≡ true  ; _ = refl

_ :  NaN      <ᵇ  NaN      ≡ false ; _ = refl
_ : -NaN      <ᵇ  NaN      ≡ false ; _ = refl
_ :  NaN      <ᵇ -NaN      ≡ false ; _ = refl
_ : -NaN      <ᵇ -NaN      ≡ false ; _ = refl
_ :  NaN      <ᵇ  5.0      ≡ false ; _ = refl
_ : -NaN      <ᵇ  5.0      ≡ false ; _ = refl
_ :  5.0      <ᵇ -NaN      ≡ false ; _ = refl
_ : -5.0      <ᵇ -NaN      ≡ false ; _ = refl
_ :  NaN      <ᵇ  Infinity ≡ false ; _ = refl
_ : -NaN      <ᵇ  Infinity ≡ false ; _ = refl
_ :  Infinity <ᵇ -NaN      ≡ false ; _ = refl
_ : -Infinity <ᵇ -NaN      ≡ false ; _ = refl
_ :  Infinity <ᵇ  Infinity ≡ false ; _ = refl
_ : -Infinity <ᵇ  Infinity ≡ true  ; _ = refl
_ :  Infinity <ᵇ -Infinity ≡ false ; _ = refl
_ : -Infinity <ᵇ -Infinity ≡ false ; _ = refl
_ :  MaxFloat <ᵇ  MaxFloat ≡ false ; _ = refl
_ :  MinFloat <ᵇ  MinFloat ≡ false ; _ = refl
_ :  1.0      <ᵇ  1.5      ≡ true  ; _ = refl
_ :  1.0      <ᵇ  1.0      ≡ false ; _ = refl
_ :  1.5      <ᵇ  1.5      ≡ false ; _ = refl

_ : isNaN  NaN      ≡ true  ; _ = refl
_ : isNaN -NaN      ≡ true  ; _ = refl
_ : isNaN  Infinity ≡ false ; _ = refl
_ : isNaN -Infinity ≡ false ; _ = refl
_ : isNaN  0.0      ≡ false ; _ = refl
_ : isNaN -0.0      ≡ false ; _ = refl
_ : isNaN  1.0      ≡ false ; _ = refl
_ : isNaN  1.5      ≡ false ; _ = refl

_ : isInfinite  NaN      ≡ false ; _ = refl
_ : isInfinite -NaN      ≡ false ; _ = refl
_ : isInfinite  Infinity ≡ true  ; _ = refl
_ : isInfinite -Infinity ≡ true  ; _ = refl
_ : isInfinite  0.0      ≡ false ; _ = refl
_ : isInfinite -0.0      ≡ false ; _ = refl
_ : isInfinite  1.0      ≡ false ; _ = refl
_ : isInfinite  1.5      ≡ false ; _ = refl

_ : isInfinite ((MaxFloat * MaxFloat) ÷ MaxFloat) ≡ true ; _ = refl

_ : isNegativeZero  NaN      ≡ false ; _ = refl
_ : isNegativeZero -NaN      ≡ false ; _ = refl
_ : isNegativeZero  Infinity ≡ false ; _ = refl
_ : isNegativeZero -Infinity ≡ false ; _ = refl
_ : isNegativeZero  0.0      ≡ false ; _ = refl
_ : isNegativeZero -0.0      ≡ true  ; _ = refl
_ : isNegativeZero  1.0      ≡ false ; _ = refl
_ : isNegativeZero  1.5      ≡ false ; _ = refl

_ : isSafeInteger 1.0         ≡ true  ; _ = refl
_ : isSafeInteger 1.5         ≡ false ; _ = refl
_ : isSafeInteger MaxFloat    ≡ false ; _ = refl
_ : isSafeInteger MinFloat    ≡ false ; _ = refl
_ : isSafeInteger MaxSafeIntF ≡ true  ; _ = refl

-- ** Conversions

_ : show  NaN      ≡  "NaN"      ; _ = refl
_ : show -NaN      ≡  "NaN"      ; _ = refl
_ : show  0.0      ≡  "0.0"      ; _ = refl
_ : show -0.0      ≡ "-0.0"      ; _ = refl
_ : show  Infinity ≡  "Infinity" ; _ = refl
_ : show -Infinity ≡ "-Infinity" ; _ = refl
_ : show  1.0      ≡  "1.0"      ; _ = refl
_ : show  1.5      ≡  "1.5"      ; _ = refl

_ : fmap toℕ (toWord 1.0)       ≡ just 4607182418800017408  ; _ = refl
_ : fmap toℕ (toWord 1.5)       ≡ just 4609434218613702656  ; _ = refl
_ : fmap toℕ (toWord 0.0)       ≡ just 0                    ; _ = refl
_ : fmap toℕ (toWord -0.0)      ≡ just 9223372036854775808  ; _ = refl
_ : fmap toℕ (toWord NaN)       ≡ nothing                   ; _ = refl
_ : fmap toℕ (toWord -NaN)      ≡ nothing                   ; _ = refl
_ : fmap toℕ (toWord Infinity)  ≡ just 9218868437227405312  ; _ = refl
_ : fmap toℕ (toWord -Infinity) ≡ just 18442240474082181120 ; _ = refl

_ : round 1.0       ≡ just (pos 1) ; _ = refl
_ : round 1.5       ≡ just (pos 2) ; _ = refl
_ : round NaN       ≡ nothing      ; _ = refl
_ : round -NaN      ≡ nothing      ; _ = refl
_ : round Infinity  ≡ nothing      ; _ = refl
_ : round -Infinity ≡ nothing      ; _ = refl
_ : round MinFloat  ≡ just (pos 0) ; _ = refl
_ : round MaxFloat  ≡ just (pos 179769313486231570814527423731704356798070567525844996598917476803157260780028538760589558632766878171540458953514382464234321326889464182768467546703537516986049910576551282076245490090389328944075868508455133942304583236903222948165808559332123348274797826204144723168738177180919299881250404026184124858368) ; _ = refl

_ : floor 1.0       ≡ just (pos 1) ; _ = refl
_ : floor 1.5       ≡ just (pos 1) ; _ = refl
_ : floor NaN       ≡ nothing      ; _ = refl
_ : floor -NaN      ≡ nothing      ; _ = refl
_ : floor Infinity  ≡ nothing      ; _ = refl
_ : floor -Infinity ≡ nothing      ; _ = refl
_ : floor MinFloat  ≡ just (pos 0) ; _ = refl
_ : floor MaxFloat  ≡ just (pos 179769313486231570814527423731704356798070567525844996598917476803157260780028538760589558632766878171540458953514382464234321326889464182768467546703537516986049910576551282076245490090389328944075868508455133942304583236903222948165808559332123348274797826204144723168738177180919299881250404026184124858368) ; _ = refl

_ : ceiling 1.0       ≡ just (pos 1) ; _ = refl
_ : ceiling 1.5       ≡ just (pos 2) ; _ = refl
_ : ceiling NaN       ≡ nothing      ; _ = refl
_ : ceiling -NaN      ≡ nothing      ; _ = refl
_ : ceiling Infinity  ≡ nothing      ; _ = refl
_ : ceiling -Infinity ≡ nothing      ; _ = refl
_ : ceiling MinFloat  ≡ just (pos 1) ; _ = refl
_ : ceiling MaxFloat  ≡ just (pos 179769313486231570814527423731704356798070567525844996598917476803157260780028538760589558632766878171540458953514382464234321326889464182768467546703537516986049910576551282076245490090389328944075868508455133942304583236903222948165808559332123348274797826204144723168738177180919299881250404026184124858368) ; _ = refl

_ : decode  NaN      ≡ nothing                           ; _ = refl
_ : decode  Infinity ≡ nothing                           ; _ = refl
_ : decode -Infinity ≡ nothing                           ; _ = refl
_ : decode  1.0      ≡ just (pos       1 , pos       0)  ; _ = refl
_ : decode  1.5      ≡ just (pos       3 , negsuc    0)  ; _ = refl
_ : decode  MaxFloat ≡ just (MaxSafeIntZ , pos     971)  ; _ = refl
_ : decode  MinFloat ≡ just (pos       1 , negsuc 1021)  ; _ = refl

_ : encode  (pos     1) (pos       0) ≡ just 1.0         ; _ = refl
_ : encode  (pos     3) (negsuc    0) ≡ just 1.5         ; _ = refl
_ : encode  MaxSafeIntZ (pos       0) ≡ just MaxSafeIntF ; _ = refl
_ : encode  MaxSafeIntZ (pos     971) ≡ just MaxFloat    ; _ = refl
_ : encode  MaxSafeIntZ (pos     972) ≡ nothing          ; _ = refl
_ : encode  (pos     1) (negsuc 1021) ≡ just MinFloat    ; _ = refl
_ : encode  MaxSafeIntZ (negsuc 1075) ≡ nothing          ; _ = refl

_ : toRatio  NaN      ≡ (pos 0    , pos 0) ; _ = refl
_ : toRatio  Infinity ≡ (pos 1    , pos 0) ; _ = refl
_ : toRatio -Infinity ≡ (negsuc 0 , pos 0) ; _ = refl
_ : toRatio  1.0      ≡ (pos 1    , pos 1) ; _ = refl
_ : toRatio  1.5      ≡ (pos 3    , pos 2) ; _ = refl

_ : fromRatio (pos 0)    (pos 0) ≡  NaN      ; _ = refl
_ : fromRatio (pos 1)    (pos 0) ≡  Infinity ; _ = refl
_ : fromRatio (negsuc 0) (pos 0) ≡ -Infinity ; _ = refl
_ : fromRatio (pos 1)    (pos 1) ≡  1.0      ; _ = refl
_ : fromRatio (pos 3)    (pos 2) ≡  1.5      ; _ = refl


_ : e^ 1.0              ≡ 2.718281828459045 ; _ = refl
_ : sin (asin 0.6)      ≡ 0.6               ; _ = refl
_ : cos (acos 0.6)      ≡ 0.6               ; _ = refl
_ : tan (atan 0.4)      ≡ 0.4               ; _ = refl
_ : tan (atan2 0.4 1.0) ≡ 0.4               ; _ = refl

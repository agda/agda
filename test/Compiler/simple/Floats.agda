module _ where

open import Common.IO
  renaming (then to _>>_
           )
open import Agda.Builtin.Unit
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
           ; primShowFloat           to showF
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
  using (Int; pos; negsuc)
  renaming ( primShowInteger         to showI
           )
open import Agda.Builtin.Nat
  using (Nat)
  renaming ( _==_                    to _==N_
           )
open import Agda.Builtin.Maybe
open import Agda.Builtin.Sigma
open import Agda.Builtin.String
  using (String)
  renaming ( primStringEquality      to _==S_
           ; primShowNat             to showN
           ; primStringAppend        to _++_
           )
open import Agda.Builtin.Word
  using (Word64)
  renaming ( primWord64ToNat         to toℕ
           )

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

MaxFloat : Float
MaxFloat = 1.7976931348623157e308

MinFloat : Float
MinFloat = 2.2250738585072014e-308

MaxSafeIntF : Float
MaxSafeIntF = 9007199254740991.0

MaxSafeIntZ : Int
MaxSafeIntZ = pos 9007199254740991

-- * Tests

showB : Bool → String
showB false = "false"
showB true  = "true"

maybeShow : {A : Set} (show : A → String) → Maybe A → String
maybeShow show (just x) = "(just (" ++ (show x ++ "))")
maybeShow show nothing  = "nothing"

pairShow : {A B : Set} (showA : A → String) (showB : B → String) → Σ A (λ _ → B) → String
pairShow showA showB (x , y) = "(" ++ (showA x ++ (" , " ++ (showB y ++ ")")))

showR = pairShow showI showI

newline : IO ⊤
newline = putStr "\n"

T : Bool → Set
T false = ⊥
T true  = ⊤

_==MW_ : Maybe Word64 → Maybe Word64 → Bool
nothing ==MW nothing = true
nothing ==MW just _  = false
just _  ==MW nothing = false
just n  ==MW just m  = toℕ n ==N toℕ m

_==F_ : Float → Float → Bool
x ==F y = toWord x ==MW toWord x

_==B_ : Bool → Bool → Bool
false ==B false = true
false ==B true  = false
true  ==B false = false
true  ==B true  = true

_==I_ : Int → Int → Bool
pos    n ==I pos    m = n ==N m
pos    n ==I negsuc m = false
negsuc n ==I pos    m = false
negsuc n ==I negsuc m = n ==N m

maybeEq : {A : Set} (eq : A → A → Bool) → Maybe A → Maybe A → Bool
maybeEq eq (just x) (just y) = eq x y
maybeEq eq (just x) nothing  = false
maybeEq eq nothing  (just y) = false
maybeEq eq nothing  nothing  = true

pairEq : {A B : Set} (eqA : A → A → Bool) (eqB : B → B → Bool) → Σ A (λ _ → B) → Σ A (λ _ → B) → Bool
pairEq eqA eqB (x , y) (z , w) = eqA x z && eqB y w
  where
    _&&_ : Bool → Bool → Bool
    true && true = true
    x    && y    = false

_==R_  = pairEq _==I_ _==I_

check : {A : Set} (show : A → String) (eq : A → A → Bool) (str : String) (exp act : A) {p : T (eq act exp)} → IO ⊤
check show eq str exp act = do
  putStr str; putStr " = "; putStr (show exp); putStr " = "; putStr (show act); newline

checkB  = check showB _==B_
checkS  = check (λ x → x) _==S_
checkN  = check showN _==N_
checkI  = check showI _==I_
checkMI = check (maybeShow showI) (maybeEq _==I_)
checkR  = check showR _==R_
checkF  = check showF _==F_
checkMR = check (maybeShow showR) (maybeEq _==R_)
checkMF = check (maybeShow showF) (maybeEq _==F_)


-- ** Relations

main : IO ⊤
main = do
  -- ** Relations
  checkB " NaN      ≡ᵇ  NaN     " false ( NaN      ≡ᵇ  NaN     )
  checkB "-NaN      ≡ᵇ  NaN     " false (-NaN      ≡ᵇ  NaN     )
  checkB " NaN      ≡ᵇ -NaN     " false ( NaN      ≡ᵇ -NaN     )
  checkB "-NaN      ≡ᵇ -NaN     " false (-NaN      ≡ᵇ -NaN     )
  checkB " Infinity ≡ᵇ  Infinity" true  ( Infinity ≡ᵇ  Infinity)
  checkB "-Infinity ≡ᵇ  Infinity" false (-Infinity ≡ᵇ  Infinity)
  checkB " Infinity ≡ᵇ -Infinity" false ( Infinity ≡ᵇ -Infinity)
  checkB "-Infinity ≡ᵇ -Infinity" true  (-Infinity ≡ᵇ -Infinity)
  checkB " MaxFloat ≡ᵇ  MaxFloat" true  ( MaxFloat ≡ᵇ  MaxFloat)
  checkB " MinFloat ≡ᵇ  MinFloat" true  ( MinFloat ≡ᵇ  MinFloat)
  checkB " 1.0      ≡ᵇ  1.5     " false ( 1.0      ≡ᵇ  1.5     )
  checkB " 1.0      ≡ᵇ  1.0     " true  ( 1.0      ≡ᵇ  1.0     )
  checkB " 1.5      ≡ᵇ  1.5     " true  ( 1.5      ≡ᵇ  1.5     )

  checkB " NaN      ≤ᵇ  NaN     " false ( NaN      ≤ᵇ  NaN     )
  checkB "-NaN      ≤ᵇ  NaN     " false (-NaN      ≤ᵇ  NaN     )
  checkB " NaN      ≤ᵇ -NaN     " false ( NaN      ≤ᵇ -NaN     )
  checkB "-NaN      ≤ᵇ -NaN     " false (-NaN      ≤ᵇ -NaN     )
  checkB " NaN      ≤ᵇ  5.0     " false ( NaN      ≤ᵇ  5.0     )
  checkB "-NaN      ≤ᵇ  5.0     " false (-NaN      ≤ᵇ  5.0     )
  checkB " 5.0      ≤ᵇ -NaN     " false ( 5.0      ≤ᵇ -NaN     )
  checkB "-5.0      ≤ᵇ -NaN     " false (-5.0      ≤ᵇ -NaN     )
  checkB " NaN      ≤ᵇ  Infinity" false ( NaN      ≤ᵇ  Infinity)
  checkB "-NaN      ≤ᵇ  Infinity" false (-NaN      ≤ᵇ  Infinity)
  checkB " Infinity ≤ᵇ -NaN     " false ( Infinity ≤ᵇ -NaN     )
  checkB "-Infinity ≤ᵇ -NaN     " false (-Infinity ≤ᵇ -NaN     )
  checkB " Infinity ≤ᵇ  Infinity" true  ( Infinity ≤ᵇ  Infinity)
  checkB "-Infinity ≤ᵇ  Infinity" true  (-Infinity ≤ᵇ  Infinity)
  checkB " Infinity ≤ᵇ -Infinity" false ( Infinity ≤ᵇ -Infinity)
  checkB "-Infinity ≤ᵇ -Infinity" true  (-Infinity ≤ᵇ -Infinity)
  checkB " MaxFloat ≤ᵇ  MaxFloat" true  ( MaxFloat ≤ᵇ  MaxFloat)
  checkB " MinFloat ≤ᵇ  MinFloat" true  ( MinFloat ≤ᵇ  MinFloat)
  checkB " 1.0      ≤ᵇ  1.5     " true  ( 1.0      ≤ᵇ  1.5     )
  checkB " 1.0      ≤ᵇ  1.0     " true  ( 1.0      ≤ᵇ  1.0     )
  checkB " 1.5      ≤ᵇ  1.5     " true  ( 1.5      ≤ᵇ  1.5     )

  checkB " NaN      <ᵇ  NaN     " false ( NaN      <ᵇ  NaN     )
  checkB "-NaN      <ᵇ  NaN     " false (-NaN      <ᵇ  NaN     )
  checkB " NaN      <ᵇ -NaN     " false ( NaN      <ᵇ -NaN     )
  checkB "-NaN      <ᵇ -NaN     " false (-NaN      <ᵇ -NaN     )
  checkB " NaN      <ᵇ  5.0     " false ( NaN      <ᵇ  5.0     )
  checkB "-NaN      <ᵇ  5.0     " false (-NaN      <ᵇ  5.0     )
  checkB " 5.0      <ᵇ -NaN     " false ( 5.0      <ᵇ -NaN     )
  checkB "-5.0      <ᵇ -NaN     " false (-5.0      <ᵇ -NaN     )
  checkB " NaN      <ᵇ  Infinity" false ( NaN      <ᵇ  Infinity)
  checkB "-NaN      <ᵇ  Infinity" false (-NaN      <ᵇ  Infinity)
  checkB " Infinity <ᵇ -NaN     " false ( Infinity <ᵇ -NaN     )
  checkB "-Infinity <ᵇ -NaN     " false (-Infinity <ᵇ -NaN     )
  checkB " Infinity <ᵇ  Infinity" false ( Infinity <ᵇ  Infinity)
  checkB "-Infinity <ᵇ  Infinity" true  (-Infinity <ᵇ  Infinity)
  checkB " Infinity <ᵇ -Infinity" false ( Infinity <ᵇ -Infinity)
  checkB "-Infinity <ᵇ -Infinity" false (-Infinity <ᵇ -Infinity)
  checkB " MaxFloat <ᵇ  MaxFloat" false ( MaxFloat <ᵇ  MaxFloat)
  checkB " MinFloat <ᵇ  MinFloat" false ( MinFloat <ᵇ  MinFloat)
  checkB " 1.0      <ᵇ  1.5     " true  ( 1.0      <ᵇ  1.5     )
  checkB " 1.0      <ᵇ  1.0     " false ( 1.0      <ᵇ  1.0     )
  checkB " 1.5      <ᵇ  1.5     " false ( 1.5      <ᵇ  1.5     )

  checkB "isNaN  NaN                " true  (isNaN  NaN                )
  checkB "isNaN -NaN                " true  (isNaN -NaN                )
  checkB "isNaN  Infinity           " false (isNaN  Infinity           )
  checkB "isNaN -Infinity           " false (isNaN -Infinity           )
  checkB "isNaN  0.0                " false (isNaN  0.0                )
  checkB "isNaN -0.0                " false (isNaN -0.0                )
  checkB "isNaN  1.0                " false (isNaN  1.0                )
  checkB "isNaN  1.5                " false (isNaN  1.5                )
  checkB "isInfinite  NaN           " false (isInfinite  NaN           )
  checkB "isInfinite -NaN           " false (isInfinite -NaN           )
  checkB "isInfinite  Infinity      " true  (isInfinite  Infinity      )
  checkB "isInfinite -Infinity      " true  (isInfinite -Infinity      )
  checkB "isInfinite  0.0           " false (isInfinite  0.0           )
  checkB "isInfinite -0.0           " false (isInfinite -0.0           )
  checkB "isInfinite  1.0           " false (isInfinite  1.0           )
  checkB "isInfinite  1.5           " false (isInfinite  1.5           )

  -- Depends on optimisation settings:
  --
  --   - with -O0 the test succeeds
  --   - with -O  the test fails
  --
  -- checkB "isInfinite ((MaxFloat * MaxFloat) ÷ MaxFloat)"
  --        true
  --        (isInfinite ((MaxFloat * MaxFloat) ÷ MaxFloat))

  checkB "isNegativeZero  NaN       " false (isNegativeZero  NaN       )
  checkB "isNegativeZero -NaN       " false (isNegativeZero -NaN       )
  checkB "isNegativeZero  Infinity  " false (isNegativeZero  Infinity  )
  checkB "isNegativeZero -Infinity  " false (isNegativeZero -Infinity  )
  checkB "isNegativeZero  0.0       " false (isNegativeZero  0.0       )
  checkB "isNegativeZero -0.0       " true  (isNegativeZero -0.0       )
  checkB "isNegativeZero  1.0       " false (isNegativeZero  1.0       )
  checkB "isNegativeZero  1.5       " false (isNegativeZero  1.5       )
  checkB "isSafeInteger 1.0         " true  (isSafeInteger 1.0         )
  checkB "isSafeInteger 1.5         " false (isSafeInteger 1.5         )
  checkB "isSafeInteger MaxFloat    " false (isSafeInteger MaxFloat    )
  checkB "isSafeInteger MinFloat    " false (isSafeInteger MinFloat    )
  checkB "isSafeInteger MaxSafeIntF " true  (isSafeInteger MaxSafeIntF )

  -- ** Conversions

  checkS "show  NaN     " "NaN"       (showF  NaN     )
  checkS "show -NaN     " "NaN"       (showF -NaN     )
  checkS "show  0.0     " "0.0"       (showF  0.0     )
  checkS "show -0.0     " "-0.0"      (showF -0.0     )
  checkS "show  Infinity" "Infinity"  (showF  Infinity)
  checkS "show -Infinity" "-Infinity" (showF -Infinity)
  checkS "show  1.0     " "1.0"       (showF  1.0     )
  checkS "show  1.5     " "1.5"       (showF  1.5     )

  -- Breaks the JavaScript backend, on account of it being... too big:
  --
  -- checkN "toℕ (toWord 1.0)      " 4607182418800017408  (toℕ (toWord 1.0)      )
  -- checkN "toℕ (toWord 1.5)      " 4609434218613702656  (toℕ (toWord 1.5)      )
  -- checkN "toℕ (toWord 0.0)      " 0                    (toℕ (toWord 0.0)      )
  -- checkN "toℕ (toWord -0.0)     " 9223372036854775808  (toℕ (toWord -0.0)     )
  -- checkN "toℕ (toWord NaN)      " 18444492273895866368 (toℕ (toWord NaN)      )
  -- checkN "toℕ (toWord -NaN)     " 18444492273895866368 (toℕ (toWord -NaN)     )
  -- checkN "toℕ (toWord Infinity) " 9218868437227405312  (toℕ (toWord Infinity) )
  -- checkN "toℕ (toWord -Infinity)" 18442240474082181120 (toℕ (toWord -Infinity))

  checkMI "round 1.0      " (just (pos 1)) (round 1.0      )
  checkMI "round 1.5      " (just (pos 2)) (round 1.5      )
  checkMI "round NaN      " (nothing     ) (round NaN      )
  checkMI "round -NaN     " (nothing     ) (round -NaN     )
  checkMI "round Infinity " (nothing     ) (round Infinity )
  checkMI "round -Infinity" (nothing     ) (round -Infinity)
  checkMI "round MinFloat " (just (pos 0)) (round MinFloat )
  --
  -- Breaks the JavaScript backend, on account of it being... too big:
  --
  -- checkMI "round MaxFloat " (just (pos 179769313486231570814527423731704356798070567525844996598917476803157260780028538760589558632766878171540458953514382464234321326889464182768467546703537516986049910576551282076245490090389328944075868508455133942304583236903222948165808559332123348274797826204144723168738177180919299881250404026184124858368)) (round MaxFloat )

  checkMI "floor 1.0      " (just (pos 1)) (floor 1.0      )
  checkMI "floor 1.5      " (just (pos 1)) (floor 1.5      )
  checkMI "floor NaN      " (nothing     ) (floor NaN      )
  checkMI "floor -NaN     " (nothing     ) (floor -NaN     )
  checkMI "floor Infinity " (nothing     ) (floor Infinity )
  checkMI "floor -Infinity" (nothing     ) (floor -Infinity)
  checkMI "floor MinFloat " (just (pos 0)) (floor MinFloat )
  --
  -- Breaks the JavaScript backend, on account of it being... too big:
  --
  -- checkMI "floor MaxFloat " (just (pos 179769313486231570814527423731704356798070567525844996598917476803157260780028538760589558632766878171540458953514382464234321326889464182768467546703537516986049910576551282076245490090389328944075868508455133942304583236903222948165808559332123348274797826204144723168738177180919299881250404026184124858368)) (floor MaxFloat )

  checkMI "ceiling 1.0      " (just (pos 1)) (ceiling 1.0      )
  checkMI "ceiling 1.5      " (just (pos 2)) (ceiling 1.5      )
  checkMI "ceiling NaN      " (nothing     ) (ceiling NaN      )
  checkMI "ceiling -NaN     " (nothing     ) (ceiling -NaN     )
  checkMI "ceiling Infinity " (nothing     ) (ceiling Infinity )
  checkMI "ceiling -Infinity" (nothing     ) (ceiling -Infinity)
  checkMI "ceiling MinFloat " (just (pos 1)) (ceiling MinFloat )
  --
  -- Breaks the JavaScript backend, on account of it being... too big:
  --
  -- checkMI "ceiling MaxFloat " (just (pos 179769313486231570814527423731704356798070567525844996598917476803157260780028538760589558632766878171540458953514382464234321326889464182768467546703537516986049910576551282076245490090389328944075868508455133942304583236903222948165808559332123348274797826204144723168738177180919299881250404026184124858368)) (ceiling MaxFloat )

  checkMR "decode  NaN     " (nothing                         ) (decode  NaN     )
  checkMR "decode  Infinity" (nothing                         ) (decode  Infinity)
  checkMR "decode -Infinity" (nothing                         ) (decode -Infinity)
  checkMR "decode  1.0     " (just (pos       1 , pos       0)) (decode  1.0     )
  checkMR "decode  1.5     " (just (pos       3 , negsuc    0)) (decode  1.5     )
  checkMR "decode  MinFloat" (just (pos       1 , negsuc 1021)) (decode  MinFloat)
  --
  -- Breaks the JavaScript backend, on account of it being... too big:
  --
  -- checkMR "decode  MaxFloat" (just (MaxSafeIntZ , pos     971)) (decode  MaxFloat)

  checkMF "encode  (pos     1) (pos       0)" (just 1.0        ) (encode  (pos     1) (pos       0))
  checkMF "encode  (pos     3) (negsuc    0)" (just 1.5        ) (encode  (pos     3) (negsuc    0))
  --
  -- Breaks the JavaScript backend, on account of it being... too big:
  --
  -- checkMF "encode  MaxSafeIntZ (pos       0)" (just MaxSafeIntF) (encode  MaxSafeIntZ (pos       0))
  -- checkMF "encode  MaxSafeIntZ (pos     971)" (just MaxFloat   ) (encode  MaxSafeIntZ (pos     971))
  -- checkMF "encode  MaxSafeIntZ (pos     972)" (nothing         ) (encode  MaxSafeIntZ (pos     972))
  -- checkMF "encode  (pos     1) (negsuc 1021)" (just MinFloat   ) (encode  (pos     1) (negsuc 1021))
  -- checkMF "encode  MaxSafeIntZ (negsuc 1075)" (nothing         ) (encode  MaxSafeIntZ (negsuc 1075))

  checkR "toRatio  NaN     " (pos 0    , pos 0) (toRatio  NaN     )
  checkR "toRatio  Infinity" (pos 1    , pos 0) (toRatio  Infinity)
  checkR "toRatio -Infinity" (negsuc 0 , pos 0) (toRatio -Infinity)
  checkR "toRatio  1.0     " (pos 1    , pos 1) (toRatio  1.0     )
  checkR "toRatio  1.5     " (pos 3    , pos 2) (toRatio  1.5     )

  checkF "fromRatio (pos 0)    (pos 0)" ( NaN     ) (fromRatio (pos 0)    (pos 0))
  checkF "fromRatio (pos 1)    (pos 0)" ( Infinity) (fromRatio (pos 1)    (pos 0))
  checkF "fromRatio (negsuc 0) (pos 0)" (-Infinity) (fromRatio (negsuc 0) (pos 0))
  checkF "fromRatio (pos 1)    (pos 1)" ( 1.0     ) (fromRatio (pos 1)    (pos 1))
  checkF "fromRatio (pos 3)    (pos 2)" ( 1.5     ) (fromRatio (pos 3)    (pos 2))

  checkF "e^ 1.0             " 2.718281828459045 (e^ 1.0             )
  checkF "sin (asin 0.6)     " 0.6               (sin (asin 0.6)     )
  checkF "cos (acos 0.6)     " 0.6               (cos (acos 0.6)     )
  checkF "tan (atan 0.4)     " 0.4               (tan (atan 0.4)     )
  checkF "tan (atan2 0.4 1.0)" 0.4               (tan (atan2 0.4 1.0))

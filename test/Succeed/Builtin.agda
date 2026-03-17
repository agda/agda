module Builtin where

open import Agda.Primitive

data Bool : Set where
  false : Bool
  true  : Bool

not : Bool -> Bool
not true = false
not false = true

_||_ : Bool -> Bool -> Bool
true  || _ = true
false || x = x

_&&_ : Bool -> Bool -> Bool
true  && x = x
false && _ = false

{-# BUILTIN BOOL  Bool  #-}
{-# BUILTIN TRUE  true  #-}
{-# BUILTIN FALSE false #-}

data Nat : Set where
  zero : Nat
  suc  : Nat -> Nat

{-# BUILTIN NATURAL Nat  #-}

zero' : Nat
zero' = 0

one : Nat
one = 1

data Int : Set where
  pos : Nat → Int
  negsuc : Nat → Int

postulate
  String : Set
  Float  : Set
  Char   : Set

{-# BUILTIN INTEGER Int    #-}
{-# BUILTIN INTEGERPOS pos #-}
{-# BUILTIN INTEGERNEGSUC negsuc #-}
{-# BUILTIN STRING  String #-}
{-# BUILTIN FLOAT   Float  #-}
{-# BUILTIN CHAR    Char   #-}

data Maybe (A : Set) : Set where
  just : A → Maybe A
  nothing : Maybe A

{-# BUILTIN MAYBE Maybe #-}

record Sigma {a b} (A : Set a) (B : A → Set b) : Set (a ⊔ b) where
  constructor _,_
  field
    fst : A
    snd : B fst

open Sigma public

infixr 4 _,_

{-# BUILTIN SIGMA Sigma #-}

infixr 10 _::_
data List (A : Set) : Set where
  nil  : List A
  _::_ : A -> List A -> List A

{-# BUILTIN LIST List   #-}

postulate Word64 : Set
{-# BUILTIN WORD64 Word64 #-}

primitive

  -- Integer functions
  primShowInteger     : Int -> String

  -- Floating point function
  primFloatInequality        : Float → Float → Bool
  primFloatEquality          : Float → Float → Bool
  primFloatLess              : Float → Float → Bool
  primFloatIsInfinite        : Float → Bool
  primFloatIsNaN             : Float → Bool
  primFloatIsNegativeZero    : Float → Bool
  primFloatToWord64          : Float → Maybe Word64
  primNatToFloat             : Nat → Float
  primIntToFloat             : Int → Float
  primFloatRound             : Float → Maybe Int
  primFloatFloor             : Float → Maybe Int
  primFloatCeiling           : Float → Maybe Int
  primFloatToRatio           : Float → (Sigma Int λ _ → Int)
  primRatioToFloat           : Int → Int → Float
  primFloatDecode            : Float → Maybe (Sigma Int λ _ → Int)
  primFloatEncode            : Int → Int → Maybe Float
  primShowFloat              : Float → String
  primFloatPlus              : Float → Float → Float
  primFloatMinus             : Float → Float → Float
  primFloatTimes             : Float → Float → Float
  primFloatDiv               : Float → Float → Float
  primFloatNegate            : Float → Float
  primFloatSqrt              : Float → Float
  primFloatExp               : Float → Float
  primFloatLog               : Float → Float
  primFloatSin               : Float → Float
  primFloatCos               : Float → Float
  primFloatTan               : Float → Float
  primFloatASin              : Float → Float
  primFloatACos              : Float → Float
  primFloatATan              : Float → Float
  primFloatATan2             : Float → Float → Float
  primFloatSinh              : Float → Float
  primFloatCosh              : Float → Float
  primFloatTanh              : Float → Float
  primFloatASinh             : Float → Float
  primFloatACosh             : Float → Float
  primFloatATanh             : Float → Float
  primFloatPow               : Float → Float → Float

   -- Character functions
  primCharEquality   : Char -> Char -> Bool
  primIsLower        : Char -> Bool
  primIsDigit        : Char -> Bool
  primIsAlpha        : Char -> Bool
  primIsSpace        : Char -> Bool
  primIsAscii        : Char -> Bool
  primIsLatin1       : Char -> Bool
  primIsPrint        : Char -> Bool
  primIsHexDigit     : Char -> Bool
  primToUpper        : Char -> Char
  primToLower        : Char -> Char
  primCharToNat      : Char -> Nat
  primNatToChar      : Nat  -> Char -- partial
  primShowChar       : Char -> String

    -- String functions
  primStringToList   : String -> List Char
  primStringFromList : List Char -> String
  primStringAppend   : String -> String -> String
  primStringEquality : String -> String -> Bool
  primShowString     : String -> String

isLower : Char -> Bool
isLower = primIsLower

isAlpha : Char -> Bool
isAlpha = primIsAlpha

isUpper : Char -> Bool
isUpper c = isAlpha c && not (isLower c)

infixl 14 _/_

nat0 = primCharToNat '\0'
int0 = pos nat0

_/_  = primFloatDiv

pi : Float
pi = 3.141592653589793

sin : Float -> Float
sin = primFloatSin

cos : Float -> Float
cos = primFloatCos

tan : Float -> Float
tan = primFloatTan

reverse : {A : Set} -> List A -> List A
reverse xs = rev xs nil
  where
    rev : {A : Set} -> List A -> List A -> List A
    rev nil       ys = ys
    rev (x :: xs) ys = rev xs (x :: ys)

infixr 20 _∘_
_∘_ : {A B C : Set} -> (B -> C) -> (A -> B) -> A -> C
f ∘ g = \x -> f (g x)

map : {A B : Set} -> (A -> B) -> List A -> List B
map f  nil      = nil
map f (x :: xs) = f x :: map f xs

stringAsList : (List Char -> List Char) -> String -> String
stringAsList f = primStringFromList ∘ f ∘ primStringToList

revStr : String -> String
revStr = stringAsList reverse

mapStr : (Char -> Char) -> String -> String
mapStr f = stringAsList (map f)

-- Testing unicode literals
uString = "åäö⊢ξ∀"
uChar   = '∀'

data _≡_ {a} {A : Set a} (x : A) : A → Set a where
  refl : x ≡ x

thm-show-pos : primShowInteger (pos 42) ≡ "42"
thm-show-pos = refl

thm-show-neg : primShowInteger (negsuc 41) ≡ "-42"
thm-show-neg = refl

thm-floor : primFloatFloor 4.2 ≡ just (pos 4)
thm-floor = refl

thm-ceiling : primFloatCeiling -5.1 ≡ just (negsuc 4)
thm-ceiling = refl

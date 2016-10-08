module Builtin where

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

infixr 10 _::_
data List (A : Set) : Set where
  nil  : List A
  _::_ : A -> List A -> List A

{-# BUILTIN LIST List   #-}
{-# BUILTIN NIL  nil    #-}
{-# BUILTIN CONS  _::_   #-}

primitive

  -- Integer functions
  primShowInteger     : Int -> String

    -- Floating point functions
  primNatToFloat     : Nat   -> Float
  primFloatPlus      : Float -> Float -> Float
  primFloatMinus     : Float -> Float -> Float
  primFloatTimes     : Float -> Float -> Float
  primFloatNegate    : Float -> Float
  primFloatDiv       : Float -> Float -> Float
  primFloatEquality  : Float -> Float -> Bool
  primFloatNumericalEquality : Float -> Float -> Bool
  primFloatNumericalLess     : Float -> Float -> Bool
  primFloatSqrt      : Float -> Float
  primRound          : Float -> Int
  primFloor          : Float -> Int
  primCeiling        : Float -> Int
  primExp            : Float -> Float
  primLog            : Float -> Float
  primSin            : Float -> Float
  primCos            : Float -> Float
  primTan            : Float -> Float
  primASin           : Float -> Float
  primACos           : Float -> Float
  primATan           : Float -> Float
  primATan2          : Float -> Float -> Float
  primShowFloat      : Float -> String

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
sin = primSin

cos : Float -> Float
cos = primCos

tan : Float -> Float
tan = primTan

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

thm-floor : primFloor 4.2 ≡ pos 4
thm-floor = refl

thm-ceiling : primCeiling -5.1 ≡ negsuc 4
thm-ceiling = refl

module builtin where

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
{-# BUILTIN SUC     suc  #-}
{-# BUILTIN ZERO    zero #-}

postulate
  Int    : Set
  String : Set
  Float  : Set
  Char   : Set

{-# BUILTIN INTEGER Int    #-}
{-# BUILTIN STRING  String #-}
{-# BUILTIN FLOAT   Float  #-}
{-# BUILTIN CHAR    Char   #-}

infixr 10 _::_
data List (A : Set) : Set where
  nil  : List A
  _::_ : A -> List A -> List A

{-# BUILTIN LIST    List   #-}
{-# BUILTIN NIL     nil    #-}
{-# BUILTIN CONS    _::_   #-}

primitive

  -- Integer functions
  primIntegerPlus     : Int -> Int -> Int
  primIntegerMinus    : Int -> Int -> Int
  primIntegerTimes    : Int -> Int -> Int
  primIntegerDiv      : Int -> Int -> Int
  primIntegerMod      : Int -> Int -> Int
  primIntegerEquality : Int -> Int -> Bool
  primIntegerLess     : Int -> Int -> Bool
  primNatToInteger    : Nat -> Int
  primShowInteger     : Int -> String

    -- Floating point functions
  primIntegerToFloat : Int -> Float
  primFloatPlus      : Float -> Float -> Float
  primFloatMinus     : Float -> Float -> Float
  primFloatTimes     : Float -> Float -> Float
  primFloatDiv       : Float -> Float -> Float
  primFloatLess      : Float -> Float -> Bool
  primRound          : Float -> Int
  primFloor          : Float -> Int
  primCeiling        : Float -> Int
  primExp            : Float -> Float
  primLog            : Float -> Float
  primSin            : Float -> Float
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

infixl 14 _*_ _/_
infix  12 -_
infixl 12 _+_ _-_
infixl 8  _==_

nat0 = primCharToNat '\0'
int0 = primNatToInteger nat0

_+_  = primIntegerPlus
_*_  = primIntegerTimes
_-_  = primIntegerMinus
-_   = \(x : Int) -> int0 - x
_==_ = primIntegerEquality
_/_  = primFloatDiv

pi = 3.141592653589793

sin = primSin

cos : Float -> Float
cos x = sin (primFloatMinus (pi / 2.0) x)

tan : Float -> Float
tan x = sin x / cos x

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


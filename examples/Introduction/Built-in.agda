
-- This module introduces built-in types and primitive functions.

module Introduction.Built-in where

{- Agda supports four built-in types :

    - integers,
    - floating point numbers,
    - characters, and
    - strings.

   Note that strings are not defined as lists of characters (as is the case in
   Haskell).

   To use the built-in types they first have to be bound to Agda types. The
   reason for this is that there are no predefined names in Agda.
-}

-- To be able to use the built-in types we first introduce a new set for each
-- built-in type.
postulate
  Int    : Set
  Float  : Set
  Char   : Set
  String : Set

-- We can then bind the built-in types to these new sets using the BUILTIN
-- pragma.
{-# BUILTIN INTEGER Int    #-}
{-# BUILTIN FLOAT   Float  #-}
{-# BUILTIN CHAR    Char   #-}
{-# BUILTIN STRING  String #-}

pi : Float
pi = 3.141593

forAll : Char
forAll = '∀'

hello : String
hello = "Hello World!"

-- There are no integer literals. Instead there are natural number literals. To
-- use these you have to tell the type checker which type to use for natural
-- numbers.

data Nat : Set where
  zero : Nat
  suc  : Nat -> Nat

{-# BUILTIN NATURAL Nat  #-}
{-# BUILTIN SUC     suc  #-}
{-# BUILTIN ZERO    zero #-}

-- Now we can define
fortyTwo : Nat
fortyTwo = 42

-- To anything interesting with values of the built-in types we need functions
-- to manipulate them. To this end Agda provides a set of primitive functions.
-- To gain access to a primitive function one simply declares it. For instance,
-- the function for floating point addition is called primFloatPlus. See below
-- for a complete list of primitive functions. At the moment the name that you
-- bring into scope is always the name of the primitive function. In the future
-- we might allow a primitive function to be introduced with any name.

module FloatPlus where  -- We put it in a module to prevent it from clashing with
                      -- the plus function in the complete list of primitive
                      -- functions below.
  primitive
    primFloatPlus : Float -> Float -> Float

  twoPi = primFloatPlus pi pi

-- Some primitive functions returns elements of non-primitive types. For
-- instance, the integer comparison functions return booleans. To be able to
-- use these functions we have to explain which type to use for booleans.

data Bool : Set where
  false : Bool
  true  : Bool

{-# BUILTIN BOOL  Bool  #-}
{-# BUILTIN TRUE  true  #-}
{-# BUILTIN FALSE false #-}

module FloatLess where

  primitive
    primFloatLess : Float -> Float -> Bool

-- There are functions to convert a string to a list of characters, so we need
-- to say which list type to use.

data List (A : Set) : Set where
  nil  : List A
  _::_ : A -> List A -> List A

{-# BUILTIN LIST List #-}
{-# BUILTIN NIL  nil  #-}
{-# BUILTIN CONS _::_ #-}

module StringToList where

  primitive
    primStringToList : String -> List Char

-- Below is a partial version of the complete list of primitive
-- functions.

primitive

    -- Integer functions
  primIntegerPlus     : Int -> Int -> Int
  primIntegerMinus    : Int -> Int -> Int
  primIntegerTimes    : Int -> Int -> Int
  primIntegerDiv      : Int -> Int -> Int  -- partial
  primIntegerMod      : Int -> Int -> Int  -- partial
  primIntegerEquality : Int -> Int -> Bool
  primIntegerLess     : Int -> Int -> Bool
  primIntegerAbs      : Int -> Nat
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
  primLog            : Float -> Float     -- partial
  primSin            : Float -> Float
  primShowFloat      : Float -> String

    -- Character functions
  primCharEquality : Char -> Char -> Bool
  primIsLower      : Char -> Bool
  primIsDigit      : Char -> Bool
  primIsAlpha      : Char -> Bool
  primIsSpace      : Char -> Bool
  primIsAscii      : Char -> Bool
  primIsLatin1     : Char -> Bool
  primIsPrint      : Char -> Bool
  primIsHexDigit   : Char -> Bool
  primToUpper      : Char -> Char
  primToLower      : Char -> Char
  primCharToNat    : Char -> Nat
  primNatToChar    : Nat  -> Char -- partial
  primShowChar     : Char -> String

    -- String functions
  primStringToList   : String -> List Char
  primStringFromList : List Char -> String
  primStringAppend   : String -> String -> String
  primStringEquality : String -> String -> Bool
  primShowString     : String -> String

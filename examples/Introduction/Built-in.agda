
-- This module introduces built-in types and primitive functions.

module Introduction.Built-in where

{- Agda supports four built-in types:

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
  Int	 : Set
  Float  : Set
  Char	 : Set
  String : Set

-- We can then bind the built-in types to these new sets using the BUILTIN
-- pragma.
{-# BUILTIN INTEGER Int	   #-}
{-# BUILTIN FLOAT   Float  #-}
{-# BUILTIN CHAR    Char   #-}
{-# BUILTIN STRING  String #-}

-- Once we've done this we can use literals of these types.
fortyTwo : Int
fortyTwo = 42

pi : Float
pi = 3.141593

forAll : Char
forAll = '∀'

hello : String
hello = "Hello World!"

-- To anything interesting with values of the built-in types we need functions
-- to manipulate them. To this end Agda provides a set of primitive functions.
-- To gain access to a primitive function one simply declares it. For instance,
-- the function for integer addition is called primIntegerPlus. See below for a
-- complete list of primitive functions. At the moment the name that you bring
-- into scope is always the name of the primitive function. In the future we
-- might allow a primitive function to be introduced with any name.

module IntPlus where  -- We put it in a module to prevent it from clashing with
		      -- the plus function in the complete list of primitive
		      -- functions below.
  primitive
    primIntegerPlus : Int -> Int -> Int

  fortySix = primIntegerPlus fortyTwo 4

-- Some primitive functions returns elements of non-primitive types. For
-- instance, the integer comparison functions return booleans. To be able to
-- use these functions we have to explain which type to use for booleans.

data Bool : Set where
  false : Bool
  true  : Bool

{-# BUILTIN BOOL  Bool  #-}
{-# BUILTIN TRUE  true  #-}
{-# BUILTIN FALSE false #-}

module IntEq where

  primitive
    primIntegerEquals : Int -> Int -> Bool

-- There are functions to convert a string to a list of characters, so we need
-- to say which list type to use.

data List (A:Set) : Set where
  nil  : List A
  _::_ : A -> List A -> List A

{-# BUILTIN LIST List #-}
{-# BUILTIN NIL  nil  #-}
{-# BUILTIN CONS _::_ #-}

module StringToList where

  primitive
    primStringToList : String -> List Char

-- There are primitive IO functions as well. These functions are treated
-- completely abstractly by the type checker, but the compiler will recognize
-- them.

postulate
  IO : Set -> Set

data Unit : Set where
  unit : Unit

{-# BUILTIN IO	 IO   #-}
{-# BUILTIN UNIT Unit #-}

module IO where

  primitive
    primPutStr : String -> IO Unit

-- Below is the complete list of primitive functions.

primitive

  -- Integer functions
  primIntegerPlus    : Int -> Int -> Int
  primIntegerMinus   : Int -> Int -> Int
  primIntegerTimes   : Int -> Int -> Int
  primIntegerDiv     : Int -> Int -> Int  -- partial
  primIntegerMod     : Int -> Int -> Int  -- partial
  primIntegerEquals  : Int -> Int -> Bool
  primIntegerLess    : Int -> Int -> Bool
  primShowInteger    : Int -> String

    -- Floating point functions
  primIntegerToFloat : Int -> Float
  primFloatPlus	     : Float -> Float -> Float
  primFloatMinus     : Float -> Float -> Float
  primFloatTimes     : Float -> Float -> Float
  primFloatDiv	     : Float -> Float -> Float
  primFloatLess	     : Float -> Float -> Bool
  primRound	     : Float -> Int
  primFloor	     : Float -> Int
  primCeiling	     : Float -> Int
  primExp	     : Float -> Float
  primLog	     : Float -> Float	  -- partial
  primSin	     : Float -> Float
  primShowFloat	     : Float -> String

    -- Character functions
  primIsLower	     : Char -> Bool
  primIsDigit	     : Char -> Bool
  primIsAlpha	     : Char -> Bool
  primIsSpace	     : Char -> Bool
  primIsAscii	     : Char -> Bool
  primIsLatin1	     : Char -> Bool
  primIsPrint	     : Char -> Bool
  primIsHexDigit     : Char -> Bool
  primToUpper	     : Char -> Char
  primToLower	     : Char -> Char
  primCharToInteger  : Char -> Int
  primIntegerToChar  : Int  -> Char -- partial
  primShowChar	     : Char -> String

    -- String functions
  primStringToList   : String -> List Char
  primStringFromList : List Char -> String
  primStringAppend   : String -> String -> String
  primStringEqual    : String -> String -> Bool
  primShowString     : String -> String

    -- IO functions (more to come)
  primPutStr	     : String -> IO Unit
  primIOReturn	     : {a:Set} -> a -> IO a
  primIOBind	     : {a,b:Set} -> IO a -> (a -> IO b) -> IO b


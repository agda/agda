
module Printf where

(∘) : {A,B,C:Set} -> (B -> C) -> (A -> B) -> A -> C
f ∘ g = \x -> f (g x)

postulate
  Int	 : Set
  String : Set
  Float  : Set
  Char	 : Set

{-# BUILTIN INTEGER Int	   #-}
{-# BUILTIN STRING  String #-}
{-# BUILTIN FLOAT   Float  #-}
{-# BUILTIN CHAR    Char   #-}

infixr 10 ::
data List (A:Set) : Set where
  nil  : List A
  (::) : A -> List A -> List A

{-# BUILTIN LIST    List   #-}
{-# BUILTIN NIL     nil    #-}
{-# BUILTIN CONS    ::     #-}

module Primitive where

  private
    primitive
      primStringAppend	 : String -> String -> String
      primStringToList	 : String -> List Char
      primStringFromList : List Char -> String
      primShowChar	 : Char -> String
      primShowInteger	 : Int -> String
      primShowFloat	 : Float -> String

  (++)	       = primStringAppend
  showChar     = primShowChar
  showInt      = primShowInteger
  showFloat    = primShowFloat
  stringToList = primStringToList
  listToString = primStringFromList

open Primitive

data FormatError (s:String) : Set where

data Unit : Set where
  unit : Unit

infixr 8 ×
infixr 8 ◅

data (×) (A,B:Set) : Set where
  (◅) : A -> B -> A × B

data Format : Set where
  stringArg : Format
  intArg    : Format
  floatArg  : Format
  charArg   : Format
  litChar   : Char -> Format
  badFormat : Char -> Format

format : String -> List Format
format = format' ∘ stringToList
  where
    format' : List Char -> List Format
    format' ('%' :: 's' :: fmt) = stringArg   :: format' fmt
    format' ('%' :: 'd' :: fmt) = intArg      :: format' fmt
    format' ('%' :: 'f' :: fmt) = floatArg    :: format' fmt
    format' ('%' :: 'c' :: fmt) = charArg     :: format' fmt
    format' ('%' :: '%' :: fmt) = litChar '%' :: format' fmt
    format' ('%' ::  c  :: fmt) = badFormat c :: format' fmt
    format' (c		:: fmt) = litChar c   :: format' fmt
    format'  nil		= nil

Printf' : List Format -> Set
Printf' (stringArg   :: fmt) = String  × Printf' fmt
Printf' (intArg      :: fmt) = Int     × Printf' fmt
Printf' (floatArg    :: fmt) = Float   × Printf' fmt
Printf' (charArg     :: fmt) = Char    × Printf' fmt
Printf' (badFormat c :: fmt) = FormatError ("Invalid % code: " ++ showChar c)
Printf' (litChar _   :: fmt) = Printf' fmt
Printf'  nil		     = Unit

Printf : String -> Set
Printf fmt = Printf' (format fmt)

printf : (fmt : String) -> Printf fmt -> String
printf fmt = printf' (format fmt)
  where
    printf' : (fmt : List Format) -> Printf' fmt -> String
    printf' (stringArg   :: fmt) (s ◅ args) = s			      ++ printf' fmt args
    printf' (intArg      :: fmt) (n ◅ args) = showInt n		      ++ printf' fmt args
    printf' (floatArg    :: fmt) (x ◅ args) = showFloat x	      ++ printf' fmt args
    printf' (charArg     :: fmt) (c ◅ args) = showChar c	      ++ printf' fmt args
    printf' (litChar c   :: fmt) args	    = listToString (c :: nil) ++ printf' fmt args
    printf' (badFormat _ :: fmt) ()	    = ?
    printf'  nil		unit	    = ""



module Printf where

_∘_ : {A : Set}{B : A -> Set}{C : {x : A} -> B x -> Set} ->
      (f : {x : A}(y : B x) -> C y)(g : (x : A) -> B x)(x : A) -> C (g x)
(f ∘ g) x = f (g x)

infixr 10 _::_
data List (A : Set) : Set where
  nil  : List A
  _::_ : A -> List A -> List A

{-# BUILTIN LIST    List   #-}
{-# BUILTIN NIL     nil    #-}
{-# BUILTIN CONS    _::_   #-}

[_] : {A : Set} -> A -> List A
[ x ] = x :: nil

module Primitive where

  postulate
    Int    : Set
    String : Set
    Float  : Set
    Char   : Set

  {-# BUILTIN INTEGER Int    #-}
  {-# BUILTIN STRING  String #-}
  {-# BUILTIN FLOAT   Float  #-}
  {-# BUILTIN CHAR    Char   #-}

  private
    primitive
      primStringAppend   : String -> String -> String
      primStringToList   : String -> List Char
      primStringFromList : List Char -> String
      primShowChar       : Char -> String
      primShowInteger    : Int -> String
      primShowFloat      : Float -> String

  _++_         = primStringAppend
  showChar     = primShowChar
  showInt      = primShowInteger
  showFloat    = primShowFloat
  stringToList = primStringToList
  listToString = primStringFromList

open Primitive

data Unit : Set where
  unit : Unit

infixr 8 _×_
infixr 8 _◅_

data _×_ (A B : Set) : Set where
  _◅_ : A -> B -> A × B

data Format : Set where
  stringArg : Format
  intArg    : Format
  floatArg  : Format
  charArg   : Format
  litChar   : Char -> Format
  badFormat : Char -> Format

data BadFormat (c : Char) : Set where

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
    format' (c          :: fmt) = litChar c   :: format' fmt
    format'  nil                = nil

Printf' : List Format -> Set
Printf' (stringArg   :: fmt) = String  × Printf' fmt
Printf' (intArg      :: fmt) = Int     × Printf' fmt
Printf' (floatArg    :: fmt) = Float   × Printf' fmt
Printf' (charArg     :: fmt) = Char    × Printf' fmt
Printf' (badFormat c :: fmt) = BadFormat c
Printf' (litChar _   :: fmt) = Printf' fmt
Printf'  nil                 = Unit

Printf : String -> Set
Printf fmt = Printf' (format fmt)

printf : (fmt : String) -> Printf fmt -> String
printf = printf' ∘ format
  where
    printf' : (fmt : List Format) -> Printf' fmt -> String
    printf' (stringArg   :: fmt) (s ◅ args) = s                  ++ printf' fmt args
    printf' (intArg      :: fmt) (n ◅ args) = showInt n          ++ printf' fmt args
    printf' (floatArg    :: fmt) (x ◅ args) = showFloat x        ++ printf' fmt args
    printf' (charArg     :: fmt) (c ◅ args) = showChar c         ++ printf' fmt args
    printf' (litChar c   :: fmt) args       = listToString [ c ] ++ printf' fmt args
    printf' (badFormat _ :: fmt) ()
    printf'  nil                 unit       = ""


-- This file starts with an (invisible) byte order mark (BOM) for utf-8.
-- (Andreas, 2023-05-08, added for issue #6524.)

module Whitespace where

-- The following definition contains several different whitespace
-- characters, and they are all treated as whitespace.

foo :  Set → Set  →  Set
foo x _ =  x

-- Tab characters are not treated as white space, but are still
-- allowed in character and string literals and non-pragma comments
-- (	).

postulate
  String : Set
  Char   : Set

{-# BUILTIN STRING  String #-}
{-# BUILTIN CHAR    Char   #-}

string : String
string = "	"

char : Char
char = '	'

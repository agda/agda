module Whitespace where

-- The following definition contains several different whitespace
-- characters, and they are all treated as whitespace.

foo :  Set -> Set  ->  Set
foo x _ =  x

-- Tab characters are not treated as white space, but are still
-- allowed in character and string literals and non-pragma comments
-- (	).

{-# BUILTIN STRING  String #-}
{-# BUILTIN CHAR    Char   #-}

string : String
string = "	"

char : Char
char = '	'

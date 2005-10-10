
{-| The parser doesn't know about fixity declarations and parses all infix
    operators left associatively, with the same precedence. This module
    contains the functions that rotates infix applications, taking precedence
    information into account.
-}
module Syntax.Concrete.Fixity where


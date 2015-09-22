module UselessPrivatePragma where

postulate Char : Set

private
  {-# BUILTIN CHAR Char #-}

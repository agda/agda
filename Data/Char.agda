------------------------------------------------------------------------
-- Characters
------------------------------------------------------------------------

module Data.Char where

open import Data.Nat
open import Data.Bool

------------------------------------------------------------------------
-- The type

postulate
  Char   : Set

{-# BUILTIN CHAR Char #-}

private
 primitive
  primCharToNat    : Char -> ℕ
  primCharEquality : Char -> Char -> Bool

toNat : Char -> ℕ
toNat = primCharToNat

infix 4 _==_

_==_ : Char -> Char -> Bool
_==_ = primCharEquality

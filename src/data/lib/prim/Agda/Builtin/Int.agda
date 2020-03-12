{-# OPTIONS --without-K --safe --no-sized-types --no-guardedness
            --no-subtyping #-}

module Agda.Builtin.Int where

open import Agda.Builtin.Nat
open import Agda.Builtin.String

infix 8 pos  -- Standard library uses this as +_

data Int : Set where
  pos    : (n : Nat) → Int
  negsuc : (n : Nat) → Int

{-# BUILTIN INTEGER       Int    #-}
{-# BUILTIN INTEGERPOS    pos    #-}
{-# BUILTIN INTEGERNEGSUC negsuc #-}

primitive primShowInteger : Int → String

{-# OPTIONS --cubical-compatible --safe --no-sized-types --no-guardedness --no-irrelevance --level-universe #-}
{-# OPTIONS -WnoFixityDeclarationForNonOperator #-}

module Agda.Builtin.Int where

open import Agda.Builtin.Nat
open import Agda.Builtin.String

-- Andreas, 2026-09-08: This fixity declaration should go
-- once downstream (std-lib, cubical) has adjusted.
infix 8 pos  -- Standard library uses this as +_

data Int : Set where
  pos    : (n : Nat) → Int
  negsuc : (n : Nat) → Int

{-# BUILTIN INTEGER       Int    #-}
{-# BUILTIN INTEGERPOS    pos    #-}
{-# BUILTIN INTEGERNEGSUC negsuc #-}

primitive primShowInteger : Int → String

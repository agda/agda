------------------------------------------------------------------------
-- The Agda standard library
--
-- Basic definitions for Characters
------------------------------------------------------------------------
module Data.Char.Base where

open import Data.Nat.Base    using (ℕ)
open import Data.Bool.Base   using (Bool)
open import Data.String.Base using (String)

------------------------------------------------------------------------
-- Re-export the type from the Core module

open import Data.Char.Core using (Char) public

------------------------------------------------------------------------
-- Primitive operations

open import Agda.Builtin.Char   public using (primCharToNat; primCharEquality)
open import Agda.Builtin.String public using (primShowChar)

show : Char → String
show = primShowChar

toNat : Char → ℕ
toNat = primCharToNat

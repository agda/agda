------------------------------------------------------------------------
-- Strings
------------------------------------------------------------------------

module Data.String where

open import Data.List using ([_])
open import Data.Char using (Char)
open import Data.Bool
open import Logic
open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality

------------------------------------------------------------------------
-- The type

postulate
  String : Set

{-# BUILTIN STRING String #-}

private
 primitive
  primStringAppend   : String -> String -> String
  primStringToList   : String -> [ Char ]
  primStringFromList : [ Char ] -> String
  primStringEquality : String -> String -> Bool

_++_ : String -> String -> String
_++_ = primStringAppend

toList : String -> [ Char ]
toList = primStringToList

fromList : [ Char ] -> String
fromList = primStringFromList

infix 4 _==_

_==_ : String -> String -> Bool
_==_ = primStringEquality

_≟_ : Decidable {String} _≡_
s₁ ≟ s₂ with s₁ == s₂
... | true  = yes trustMe
  where postulate trustMe : _
... | false = no trustMe
  where postulate trustMe : _

setoid : Setoid
setoid = ≡-setoid String

decSetoid : DecSetoid
decSetoid = record { setoid = setoid; _≟_ = _≟_ }

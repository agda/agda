------------------------------------------------------------------------
-- Strings
------------------------------------------------------------------------

module Data.String where

import Data.List as List
open List using ([_])
import Data.Vec as Vec
open Vec using (Vec)
import Data.Colist as Colist
open Colist using (Colist)
open import Data.Char using (Char)
open import Data.Bool
open import Data.Function
open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality

------------------------------------------------------------------------
-- Types

-- Finite strings.

postulate
  String : Set

{-# BUILTIN STRING String #-}
{-# COMPILED_TYPE String String #-}

-- Possibly infinite strings.

Costring : Set
Costring = Colist Char

------------------------------------------------------------------------
-- Operations

private
 primitive
  primStringAppend   : String -> String -> String
  primStringToList   : String -> [ Char ]
  primStringFromList : [ Char ] -> String
  primStringEquality : String -> String -> Bool

infixr 5 _++_

_++_ : String -> String -> String
_++_ = primStringAppend

toList : String -> [ Char ]
toList = primStringToList

fromList : [ Char ] -> String
fromList = primStringFromList

toVec : (s : String) -> Vec Char (List.length (toList s))
toVec s = Vec.fromList (toList s)

toCostring : String -> Costring
toCostring = Colist.fromList ∘ toList

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
decSetoid = ≡-decSetoid _≟_

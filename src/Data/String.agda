------------------------------------------------------------------------
-- The Agda standard library
--
-- Strings
------------------------------------------------------------------------

module Data.String where

open import Data.List as List using (_∷_; []; List)
open import Data.Vec as Vec using (Vec)
open import Data.Colist as Colist using (Colist)
open import Data.Char as Char using (Char)
open import Data.Bool using (Bool; true; false)
open import Function
open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.List.StrictLex as StrictLex
import Relation.Binary.On as On
open import Relation.Binary.PropositionalEquality as PropEq using (_≡_)
open import Relation.Binary.PropositionalEquality.TrustMe

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
  primStringAppend   : String → String → String
  primStringToList   : String → List Char
  primStringFromList : List Char → String
  primStringEquality : String → String → Bool

infixr 5 _++_

_++_ : String → String → String
_++_ = primStringAppend

toList : String → List Char
toList = primStringToList

fromList : List Char → String
fromList = primStringFromList

toVec : (s : String) → Vec Char (List.length (toList s))
toVec s = Vec.fromList (toList s)

toCostring : String → Costring
toCostring = Colist.fromList ∘ toList

unlines : List String → String
unlines []       = ""
unlines (x ∷ xs) = x ++ "\n" ++ unlines xs

infix 4 _==_

_==_ : String → String → Bool
_==_ = primStringEquality

_≟_ : Decidable {A = String} _≡_
s₁ ≟ s₂ with s₁ == s₂
... | true  = yes trustMe
... | false = no whatever
  where postulate whatever : _

setoid : Setoid _ _
setoid = PropEq.setoid String

decSetoid : DecSetoid _ _
decSetoid = PropEq.decSetoid _≟_

-- Lexicographic ordering of strings.

strictTotalOrder : StrictTotalOrder _ _ _
strictTotalOrder =
  On.strictTotalOrder
    (StrictLex.<-strictTotalOrder Char.strictTotalOrder)
    toList

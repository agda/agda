------------------------------------------------------------------------
-- The Agda standard library
--
-- Strings
------------------------------------------------------------------------

module Data.String.Base where

open import Data.List.Base as List using (_∷_; []; List)
open import Data.Bool.Base using (Bool)
open import Data.Char.Core using (Char)
open import Relation.Binary.Core using (_≡_)
open import Relation.Binary.PropositionalEquality.TrustMe using (trustMe)

------------------------------------------------------------------------
-- From Agda.Builtin

open import Agda.Builtin.String public
  using ( String
        ; primStringAppend
        ; primStringToList
        ; primStringFromList
        ; primStringEquality
        ; primShowString )

------------------------------------------------------------------------
-- Operations

infixr 5 _++_

_++_ : String → String → String
_++_ = primStringAppend

toList : String → List Char
toList = primStringToList

fromList : List Char → String
fromList = primStringFromList

toList∘fromList : ∀ s → toList (fromList s) ≡ s
toList∘fromList s = trustMe

fromList∘toList : ∀ s → fromList (toList s) ≡ s
fromList∘toList s = trustMe

unlines : List String → String
unlines []       = ""
unlines (x ∷ xs) = x ++ "\n" ++ unlines xs

show : String → String
show = primShowString

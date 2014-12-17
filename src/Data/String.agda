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
open import Data.Bool.Minimal using (Bool; true; false)
open import Function
open import Relation.Nullary
open import Relation.Nullary.Decidable
open import Relation.Binary
open import Relation.Binary.List.StrictLex as StrictLex
import Relation.Binary.On as On
open import Relation.Binary.PropositionalEquality as PropEq using (_≡_)
open import Relation.Binary.PropositionalEquality.TrustMe

import Data.String.Core as Core
open Core public using (String)
open Core

-- Possibly infinite strings.

Costring : Set
Costring = Colist Char

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

toVec : (s : String) → Vec Char (List.length (toList s))
toVec s = Vec.fromList (toList s)

toCostring : String → Costring
toCostring = Colist.fromList ∘ toList

unlines : List String → String
unlines []       = ""
unlines (x ∷ xs) = x ++ "\n" ++ unlines xs

show : String → String
show = primShowString

-- Informative equality test.

_≟_ : Decidable {A = String} _≡_
s₁ ≟ s₂ with primStringEquality s₁ s₂
... | true  = yes trustMe
... | false = no whatever
  where postulate whatever : _

-- Boolean equality test.
--
-- Why is the definition _==_ = primStringEquality not used? One
-- reason is that the present definition can sometimes improve type
-- inference, at least with the version of Agda that is current at the
-- time of writing: see unit-test below.

infix 4 _==_

_==_ : String → String → Bool
s₁ == s₂ = ⌊ s₁ ≟ s₂ ⌋

private

  -- The following unit test does not type-check (at the time of
  -- writing) if _==_ is replaced by primStringEquality.

  data P : (String → Bool) → Set where
    p : (c : String) → P (_==_ c)

  unit-test : P (_==_ "")
  unit-test = p _

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

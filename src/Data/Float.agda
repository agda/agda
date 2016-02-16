------------------------------------------------------------------------
-- The Agda standard library
--
-- Floats
------------------------------------------------------------------------

module Data.Float where

open import Data.Bool.Base using (Bool; false; true)
open import Relation.Nullary.Decidable
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality as PropEq using (_≡_)
open import Relation.Binary.PropositionalEquality.TrustMe
open import Data.String.Base using (String)

open import Agda.Builtin.Float public
  using ( Float; primFloatEquality; primShowFloat )

show : Float → String
show = primShowFloat

infix 4 _≟_

_≟_ : (x y : Float) → Dec (x ≡ y)
x ≟ y with primFloatEquality x y
... | true  = yes trustMe
... | false = no whatever
  where postulate whatever : _

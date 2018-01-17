------------------------------------------------------------------------
-- The Agda standard library
--
-- Characters
------------------------------------------------------------------------

module Data.Char where

open import Data.Nat.Base using (ℕ)
open import Data.Nat.Properties using (<-strictTotalOrder)
open import Data.Bool.Base using (Bool; true; false)
open import Relation.Nullary
open import Relation.Nullary.Decidable
open import Relation.Binary
import Relation.Binary.On as On
open import Relation.Binary.PropositionalEquality as PropEq using (_≡_)
open import Relation.Binary.PropositionalEquality.TrustMe

open import Agda.Builtin.Char using (primCharEquality)
open import Data.String.Base using (String)
open import Data.Char.Base
open        Data.Char.Base public using (Char; show; toNat; fromNat)

-- Informative equality test.

infix 4 _≟_

_≟_ : Decidable {A = Char} _≡_
s₁ ≟ s₂ with primCharEquality s₁ s₂
... | true  = yes trustMe
... | false = no whatever
  where postulate whatever : _

-- Boolean equality test.
--
-- Why is the definition _==_ = primCharEquality not used? One reason
-- is that the present definition can sometimes improve type
-- inference, at least with the version of Agda that is current at the
-- time of writing: see unit-test below.

infix 4 _==_

_==_ : Char → Char → Bool
c₁ == c₂ = ⌊ c₁ ≟ c₂ ⌋

private

  -- The following unit test does not type-check (at the time of
  -- writing) if _==_ is replaced by primCharEquality.

  data P : (Char → Bool) → Set where
    p : (c : Char) → P (_==_ c)

  unit-test : P (_==_ 'x')
  unit-test = p _

setoid : Setoid _ _
setoid = PropEq.setoid Char

decSetoid : DecSetoid _ _
decSetoid = PropEq.decSetoid _≟_

-- An ordering induced by the toNat function.

strictTotalOrder : StrictTotalOrder _ _ _
strictTotalOrder = On.strictTotalOrder <-strictTotalOrder toNat

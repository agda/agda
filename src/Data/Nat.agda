------------------------------------------------------------------------
-- The Agda standard library
--
-- Natural numbers
------------------------------------------------------------------------

module Data.Nat where

open import Function
open import Function.Equality as F using (_⟨$⟩_)
open import Function.Injection using (_↣_)
open import Data.Sum
open import Data.Empty
import Level
open import Relation.Nullary
import Relation.Nullary.Decidable as Dec
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as PropEq
  using (_≡_; refl)

-- The core type and operations are re-exported from Data.Nat.Base
open import Data.Nat.Base public

-- If there is an injection from a type to ℕ, then the type has
-- decidable equality.

eq? : ∀ {a} {A : Set a} → A ↣ ℕ → Decidable {A = A} _≡_
eq? inj = Dec.via-injection inj _≟_

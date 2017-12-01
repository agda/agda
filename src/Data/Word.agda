------------------------------------------------------------------------
-- The Agda standard library
--
-- Machine words
------------------------------------------------------------------------

module Data.Word where

open import Data.Nat.Base renaming (_≟_ to _≟ℕ_)
import Agda.Builtin.Word as Builtin
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality.TrustMe

open Builtin using (Word64) public
open Builtin

toℕ : Word64 → ℕ
toℕ = primWord64ToNat

fromℕ : ℕ → Word64
fromℕ = primWord64FromNat

_≟_ : (a b : Word64) → Dec (a ≡ b)
a ≟ b with toℕ a ≟ℕ toℕ b
... | yes _ = yes trustMe
... | no  _ = no whatever
  where postulate whatever : _

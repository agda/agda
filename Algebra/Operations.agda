------------------------------------------------------------------------
-- Some defined operations (multiplication by natural number and
-- exponentiation)
------------------------------------------------------------------------

open import Algebra

module Algebra.Operations (s : Semiring) where

open Semiring s hiding (zero)
open import Data.Nat using (zero; suc; ℕ)
open import Data.Function
open import Logic
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
import Relation.Binary.EqReasoning as EqR
open EqR setoid

------------------------------------------------------------------------
-- Operations

-- Multiplication by natural number.

infixr 7 _×_

_×_ : ℕ -> carrier -> carrier
zero  × x = 0#
suc n × x = x + n × x

-- Exponentiation.

infixr 8 _^_

_^_ : carrier -> ℕ -> carrier
x ^ zero  = 1#
x ^ suc n = x * x ^ n

------------------------------------------------------------------------
-- Some properties

abstract

  ×-pres-≈ : _×_ Preserves₂ _≡_ → _≈_ → _≈_
  ×-pres-≈ {n} {n'} {x} {x'} n≡n' x≈x' = begin
    n  × x   ≈⟨ reflexive $ ≡-cong (\n -> n × x) n≡n' ⟩
    n' × x   ≈⟨ ×-pres-≈ʳ n' x≈x' ⟩
    n' × x'  ∎
    where
    ×-pres-≈ʳ : forall n -> (_×_ n) Preserves _≈_ → _≈_
    ×-pres-≈ʳ zero    x≈x' = byDef
    ×-pres-≈ʳ (suc n) x≈x' = x≈x' ⟨ +-pres-≈ ⟩ ×-pres-≈ʳ n x≈x'

  ^-pres-≈ : _^_ Preserves₂ _≈_ → _≡_ → _≈_
  ^-pres-≈ {x} {x'} {n} {n'} x≈x' n≡n' = begin
    x  ^ n   ≈⟨ reflexive $ ≡-cong (_^_ x) n≡n' ⟩
    x  ^ n'  ≈⟨ ^-pres-≈ˡ n' x≈x' ⟩
    x' ^ n'  ∎
    where
    ^-pres-≈ˡ : forall n -> (\x -> x ^ n) Preserves _≈_ → _≈_
    ^-pres-≈ˡ zero    x≈x' = byDef
    ^-pres-≈ˡ (suc n) x≈x' = x≈x' ⟨ *-pres-≈ ⟩ ^-pres-≈ˡ n x≈x'

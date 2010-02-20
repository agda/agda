------------------------------------------------------------------------
-- Some defined operations (multiplication by natural number and
-- exponentiation)
------------------------------------------------------------------------

{-# OPTIONS --universe-polymorphism #-}

open import Algebra

module Algebra.Operations {s₁ s₂} (S : Semiring s₁ s₂) where

open Semiring S hiding (zero)
open import Data.Nat using (zero; suc; ℕ)
open import Function
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as PropEq using (_≡_)
import Relation.Binary.EqReasoning as EqR
open EqR setoid

------------------------------------------------------------------------
-- Operations

-- Multiplication by natural number.

infixr 7 _×_

_×_ : ℕ → Carrier → Carrier
zero  × x = 0#
suc n × x = x + n × x

-- Exponentiation.

infixr 8 _^_

_^_ : Carrier → ℕ → Carrier
x ^ zero  = 1#
x ^ suc n = x * x ^ n

------------------------------------------------------------------------
-- Some properties

×-cong : _×_ Preserves₂ _≡_ ⟶ _≈_ ⟶ _≈_
×-cong {n} {n'} {x} {x'} n≡n' x≈x' = begin
  n  × x   ≈⟨ reflexive $ PropEq.cong (λ n → n × x) n≡n' ⟩
  n' × x   ≈⟨ ×-congʳ n' x≈x' ⟩
  n' × x'  ∎
  where
  ×-congʳ : ∀ n → (_×_ n) Preserves _≈_ ⟶ _≈_
  ×-congʳ zero    x≈x' = refl
  ×-congʳ (suc n) x≈x' = x≈x' ⟨ +-cong ⟩ ×-congʳ n x≈x'

^-cong : _^_ Preserves₂ _≈_ ⟶ _≡_ ⟶ _≈_
^-cong {x} {x'} {n} {n'} x≈x' n≡n' = begin
  x  ^ n   ≈⟨ reflexive $ PropEq.cong (_^_ x) n≡n' ⟩
  x  ^ n'  ≈⟨ ^-congˡ n' x≈x' ⟩
  x' ^ n'  ∎
  where
  ^-congˡ : ∀ n → (λ x → x ^ n) Preserves _≈_ ⟶ _≈_
  ^-congˡ zero    x≈x' = refl
  ^-congˡ (suc n) x≈x' = x≈x' ⟨ *-cong ⟩ ^-congˡ n x≈x'

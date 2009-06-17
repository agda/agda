------------------------------------------------------------------------
-- Rational numbers
------------------------------------------------------------------------

module Data.Rational where

open import Data.Bool.Properties
open import Data.Function
open import Data.Integer hiding (suc) renaming (_*_ to _ℤ*_)
open import Data.Integer.Divisibility as ℤDiv using (Coprime)
import Data.Integer.Properties as ℤ
open import Data.Nat.Divisibility as ℕDiv using (_∣_)
import Data.Nat.Coprimality as C
open import Data.Nat as ℕ renaming (_*_ to _ℕ*_)
open import Relation.Nullary.Decidable
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as PropEq
open ≡-Reasoning

------------------------------------------------------------------------
-- The definition

-- Rational numbers in reduced form.

record ℚ : Set where
  field
    numerator     : ℤ
    denominator-1 : ℕ
    isCoprime     : True (C.coprime? ∣ numerator ∣ (suc denominator-1))

  denominator : ℤ
  denominator = + suc denominator-1

  coprime : Coprime numerator denominator
  coprime = witnessToTruth isCoprime

-- Constructs rational numbers. The arguments have to be in reduced
-- form.

infixl 7 _÷_

_÷_ : (numerator : ℤ) (denominator : ℕ)
      {coprime : True (C.coprime? ∣ numerator ∣ denominator)}
      {≢0 : False (ℕ._≟_ denominator 0)} →
      ℚ
(n ÷ zero) {≢0 = ()}
(n ÷ suc d) {c} =
  record { numerator = n; denominator-1 = d; isCoprime = c }

private

  -- Note that the implicit arguments do not need to be given for
  -- concrete inputs:

  0/1 : ℚ
  0/1 = + 0 ÷ 1

  -½ : ℚ
  -½ = - + 1 ÷ 2

------------------------------------------------------------------------
-- Equality

-- Equality of rational numbers.

infix 4 _≃_

_≃_ : Rel ℚ
p ≃ q = P.numerator ℤ* Q.denominator ≡
        Q.numerator ℤ* P.denominator
  where module P = ℚ p; module Q = ℚ q

-- _≃_ coincides with propositional equality.

≡⇒≃ : _≡_ ⇒ _≃_
≡⇒≃ refl = refl

≃⇒≡ : _≃_ ⇒ _≡_
≃⇒≡ {p} {q} = helper P.numerator P.denominator-1 P.isCoprime
                     Q.numerator Q.denominator-1 Q.isCoprime
  where
  module P = ℚ p; module Q = ℚ q

  helper : ∀ n₁ d₁ c₁ n₂ d₂ c₂ →
           n₁ ℤ* + suc d₂ ≡ n₂ ℤ* + suc d₁ →
           (n₁ ÷ suc d₁) {c₁} ≡ (n₂ ÷ suc d₂) {c₂}
  helper n₁ d₁ c₁ n₂ d₂ c₂ eq
    with Poset.antisym ℕDiv.poset 1+d₁∣1+d₂ 1+d₂∣1+d₁
    where
    1+d₁∣1+d₂ : suc d₁ ∣ suc d₂
    1+d₁∣1+d₂ = ℤDiv.coprime-divisor (+ suc d₁) n₁ (+ suc d₂)
                  (C.sym $ witnessToTruth c₁) $
                  ℕDiv.divides ∣ n₂ ∣ (begin
                    ∣ n₁ ℤ* + suc d₂ ∣  ≡⟨ cong ∣_∣ eq ⟩
                    ∣ n₂ ℤ* + suc d₁ ∣  ≡⟨ ℤ.abs-*-commute n₂ (+ suc d₁) ⟩
                    ∣ n₂ ∣ ℕ* suc d₁    ∎)

    1+d₂∣1+d₁ : suc d₂ ∣ suc d₁
    1+d₂∣1+d₁ = ℤDiv.coprime-divisor (+ suc d₂) n₂ (+ suc d₁)
                  (C.sym $ witnessToTruth c₂) $
                  ℕDiv.divides ∣ n₁ ∣ (begin
                    ∣ n₂ ℤ* + suc d₁ ∣  ≡⟨ cong ∣_∣ (PropEq.sym eq) ⟩
                    ∣ n₁ ℤ* + suc d₂ ∣  ≡⟨ ℤ.abs-*-commute n₁ (+ suc d₂) ⟩
                    ∣ n₁ ∣ ℕ* suc d₂    ∎)

  helper n₁ d c₁ n₂ .d c₂ eq | refl with ℤ.cancel-*-right
                                           n₁ n₂ (+ suc d) (λ ()) eq
  helper n  d c₁ .n .d c₂ eq | refl | refl with proof-irrelevance c₁ c₂
  helper n  d c  .n .d .c eq | refl | refl | refl = refl

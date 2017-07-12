------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of Rational numbers
------------------------------------------------------------------------

module Data.Rational.Properties where

import Algebra
open import Function using (_∘_)
import Data.Integer as ℤ
import Data.Integer.Properties as ℤₚ
open import Data.Rational
open import Data.Nat as ℕ using (ℕ; zero; suc)
open import Data.Sum
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as P
  using (_≡_; refl; sym; cong; cong₂)

------------------------------------------------------------------------
-- _≤_

≤-reflexive : _≡_ ⇒ _≤_
≤-reflexive refl = *≤* ℤₚ.≤-refl

≤-refl : Reflexive _≤_
≤-refl = ≤-reflexive refl

≤-trans : Transitive _≤_
≤-trans {i = p} {j = q} {k = r} (*≤* le₁) (*≤* le₂)
  = *≤* (ℤₚ.cancel-*-+-right-≤ _ _ _
          (lemma
            (ℚ.numerator p) (ℚ.denominator p)
            (ℚ.numerator q) (ℚ.denominator q)
            (ℚ.numerator r) (ℚ.denominator r)
            (ℤₚ.*-+-right-mono (ℚ.denominator-1 r) le₁)
            (ℤₚ.*-+-right-mono (ℚ.denominator-1 p) le₂)))
  where
  lemma : ∀ n₁ d₁ n₂ d₂ n₃ d₃ →
          n₁ ℤ.* d₂ ℤ.* d₃ ℤ.≤ n₂ ℤ.* d₁ ℤ.* d₃ →
          n₂ ℤ.* d₃ ℤ.* d₁ ℤ.≤ n₃ ℤ.* d₂ ℤ.* d₁ →
          n₁ ℤ.* d₃ ℤ.* d₂ ℤ.≤ n₃ ℤ.* d₁ ℤ.* d₂
  lemma n₁ d₁ n₂ d₂ n₃ d₃
    rewrite ℤₚ.*-assoc n₁ d₂ d₃
          | ℤₚ.*-comm d₂ d₃
          | sym (ℤₚ.*-assoc n₁ d₃ d₂)
          | ℤₚ.*-assoc n₃ d₂ d₁
          | ℤₚ.*-comm d₂ d₁
          | sym (ℤₚ.*-assoc n₃ d₁ d₂)
          | ℤₚ.*-assoc n₂ d₁ d₃
          | ℤₚ.*-comm d₁ d₃
          | sym (ℤₚ.*-assoc n₂ d₃ d₁)
          = ℤₚ.≤-trans

≤-antisym : Antisymmetric _≡_ _≤_
≤-antisym (*≤* le₁) (*≤* le₂) = ≃⇒≡ (ℤₚ.≤-antisym le₁ le₂)

≤-total : Total _≤_
≤-total p q =
  [ inj₁ ∘ *≤* , inj₂ ∘ *≤* ]′
    (ℤₚ.≤-total (ℚ.numerator p ℤ.* ℚ.denominator q)
              (ℚ.numerator q ℤ.* ℚ.denominator p))

≤-isPreorder : IsPreorder _≡_ _≤_
≤-isPreorder = record
  { isEquivalence = P.isEquivalence
  ; reflexive     = ≤-reflexive
  ; trans         = ≤-trans
  }

≤-isPartialOrder : IsPartialOrder _≡_ _≤_
≤-isPartialOrder = record
  { isPreorder = ≤-isPreorder
  ; antisym    = ≤-antisym
  }

≤-isTotalOrder : IsTotalOrder _≡_ _≤_
≤-isTotalOrder = record
  { isPartialOrder = ≤-isPartialOrder
  ; total          = ≤-total
  }

≤-isDecTotalOrder : IsDecTotalOrder _≡_ _≤_
≤-isDecTotalOrder = record
  { isTotalOrder = ≤-isTotalOrder
  ; _≟_          = _≟_
  ; _≤?_         = _≤?_
  }

≤-decTotalOrder : DecTotalOrder _ _ _
≤-decTotalOrder = record
  { Carrier         = ℚ
  ; _≈_             = _≡_
  ; _≤_             = _≤_
  ; isDecTotalOrder = ≤-isDecTotalOrder
  }


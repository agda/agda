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

------------------------------------------------------------------------
-- Some properties

decTotalOrder : DecTotalOrder _ _ _
decTotalOrder = record
  { Carrier         = ℕ
  ; _≈_             = _≡_
  ; _≤_             = _≤_
  ; isDecTotalOrder = record
      { isTotalOrder = record
          { isPartialOrder = record
              { isPreorder = record
                  { isEquivalence = PropEq.isEquivalence
                  ; reflexive     = refl′
                  ; trans         = trans
                  }
              ; antisym  = antisym
              }
          ; total = total
          }
      ; _≟_  = _≟_
      ; _≤?_ = _≤?_
      }
  }
  where
  refl′ : _≡_ ⇒ _≤_
  refl′ {zero}  refl = z≤n
  refl′ {suc m} refl = s≤s (refl′ refl)

  antisym : Antisymmetric _≡_ _≤_
  antisym z≤n       z≤n       = refl
  antisym (s≤s m≤n) (s≤s n≤m) with antisym m≤n n≤m
  ...                         | refl = refl

  trans : Transitive _≤_
  trans z≤n       _         = z≤n
  trans (s≤s m≤n) (s≤s n≤o) = s≤s (trans m≤n n≤o)

  total : Total _≤_
  total zero    _       = inj₁ z≤n
  total _       zero    = inj₂ z≤n
  total (suc m) (suc n) with total m n
  ...                   | inj₁ m≤n = inj₁ (s≤s m≤n)
  ...                   | inj₂ n≤m = inj₂ (s≤s n≤m)

import Relation.Binary.PartialOrderReasoning as POR
module ≤-Reasoning where
  open POR (DecTotalOrder.poset decTotalOrder) public
    renaming (_≈⟨_⟩_ to _≡⟨_⟩_)

  infixr 2 _<⟨_⟩_

  _<⟨_⟩_ : ∀ x {y z} → x < y → y IsRelatedTo z → suc x IsRelatedTo z
  x <⟨ x<y ⟩ y≤z = suc x ≤⟨ x<y ⟩ y≤z

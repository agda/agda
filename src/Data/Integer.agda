------------------------------------------------------------------------
-- The Agda standard library
--
-- Integers
------------------------------------------------------------------------

module Data.Integer where

import Data.Nat as ℕ
import Data.Nat.Show as ℕ
open import Data.Sign as Sign using (Sign)
open import Data.String.Base using (String; _++_)
open import Function
open import Data.Sum
open import Relation.Nullary
import Relation.Nullary.Decidable as Dec
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as PropEq
  using (_≡_; refl; sym; cong; cong₂)
open PropEq.≡-Reasoning

------------------------------------------------------------------------
-- Integers, basic types and operations

open import Data.Integer.Base public

------------------------------------------------------------------------
-- Conversions

-- Decimal string representation.

show : ℤ → String
show i = showSign (sign i) ++ ℕ.show ∣ i ∣
  where
  showSign : Sign → String
  showSign Sign.- = "-"
  showSign Sign.+ = ""

------------------------------------------------------------------------
-- Properties of the view of integers as sign + absolute value

◃-cong : ∀ {i j} → sign i ≡ sign j → ∣ i ∣ ≡ ∣ j ∣ → i ≡ j
◃-cong {i} {j} sign-≡ abs-≡ = begin
  i               ≡⟨ sym $ ◃-left-inverse i ⟩
  sign i ◃ ∣ i ∣  ≡⟨ cong₂ _◃_ sign-≡ abs-≡ ⟩
  sign j ◃ ∣ j ∣  ≡⟨ ◃-left-inverse j ⟩
  j               ∎

signAbs : ∀ i → SignAbs i
signAbs i = PropEq.subst SignAbs (◃-left-inverse i) $
              sign i ◂ ∣ i ∣

------------------------------------------------------------------------
-- Equality is decidable

infix 4 _≟_

_≟_ : Decidable {A = ℤ} _≡_
i ≟ j with Sign._≟_ (sign i) (sign j) | ℕ._≟_ ∣ i ∣ ∣ j ∣
i ≟ j | yes sign-≡ | yes abs-≡ = yes (◃-cong sign-≡ abs-≡)
i ≟ j | no  sign-≢ | _         = no (sign-≢ ∘ cong sign)
i ≟ j | _          | no abs-≢  = no (abs-≢  ∘ cong ∣_∣)

decSetoid : DecSetoid _ _
decSetoid = PropEq.decSetoid _≟_

------------------------------------------------------------------------
-- Ordering

infix  4 _≤?_

_≤?_ : Decidable _≤_
-[1+ m ] ≤? -[1+ n ] = Dec.map′ -≤- drop‿-≤- (ℕ._≤?_ n m)
-[1+ m ] ≤? +    n   = yes -≤+
+    m   ≤? -[1+ n ] = no λ ()
+    m   ≤? +    n   = Dec.map′ +≤+ drop‿+≤+ (ℕ._≤?_ m n)

decTotalOrder : DecTotalOrder _ _ _
decTotalOrder = record
  { Carrier         = ℤ
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
          ; total          = total
          }
      ; _≟_          = _≟_
      ; _≤?_         = _≤?_
      }
  }
  where
  module ℕO = DecTotalOrder ℕ.decTotalOrder

  refl′ : _≡_ ⇒ _≤_
  refl′ { -[1+ n ]} refl = -≤- ℕO.refl
  refl′ {+ n}       refl = +≤+ ℕO.refl

  trans : Transitive _≤_
  trans -≤+       (+≤+ n≤m) = -≤+
  trans (-≤- n≤m) -≤+       = -≤+
  trans (-≤- n≤m) (-≤- k≤n) = -≤- (ℕO.trans k≤n n≤m)
  trans (+≤+ m≤n) (+≤+ n≤k) = +≤+ (ℕO.trans m≤n n≤k)

  antisym : Antisymmetric _≡_ _≤_
  antisym -≤+       ()
  antisym (-≤- n≤m) (-≤- m≤n) = cong -[1+_] $ ℕO.antisym m≤n n≤m
  antisym (+≤+ m≤n) (+≤+ n≤m) = cong +_     $ ℕO.antisym m≤n n≤m

  total : Total _≤_
  total (-[1+ m ]) (-[1+ n ]) = [ inj₂ ∘′ -≤- , inj₁ ∘′ -≤- ]′ $ ℕO.total m n
  total (-[1+ m ]) (+    n  ) = inj₁ -≤+
  total (+    m  ) (-[1+ n ]) = inj₂ -≤+
  total (+    m  ) (+    n  ) = [ inj₁ ∘′ +≤+ , inj₂ ∘′ +≤+ ]′ $ ℕO.total m n

poset : Poset _ _ _
poset = DecTotalOrder.poset decTotalOrder

import Relation.Binary.PartialOrderReasoning as POR
module ≤-Reasoning = POR poset
  renaming (_≈⟨_⟩_ to _≡⟨_⟩_)

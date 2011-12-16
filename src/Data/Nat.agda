------------------------------------------------------------------------
-- The Agda standard library
--
-- Natural numbers
------------------------------------------------------------------------

module Data.Nat where

open import Function
open import Function.Equality as F using (_⟨$⟩_)
open import Function.Injection
  using (Injection; module Injection)
open import Data.Sum
open import Data.Empty
import Level
open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as PropEq
  using (_≡_; refl)

infixl 7 _*_ _⊓_
infixl 6 _∸_ _⊔_

------------------------------------------------------------------------
-- The types

data ℕ : Set where
  zero : ℕ
  suc  : (n : ℕ) → ℕ

{-# BUILTIN NATURAL ℕ    #-}
{-# BUILTIN ZERO    zero #-}
{-# BUILTIN SUC     suc  #-}

infix 4 _≤_ _<_ _≥_ _>_ _≰_ _≮_ _≱_ _≯_

data _≤_ : Rel ℕ Level.zero where
  z≤n : ∀ {n}                 → zero  ≤ n
  s≤s : ∀ {m n} (m≤n : m ≤ n) → suc m ≤ suc n

_<_ : Rel ℕ Level.zero
m < n = suc m ≤ n

_≥_ : Rel ℕ Level.zero
m ≥ n = n ≤ m

_>_ : Rel ℕ Level.zero
m > n = n < m

_≰_ : Rel ℕ Level.zero
a ≰ b = ¬ a ≤ b

_≮_ : Rel ℕ Level.zero
a ≮ b = ¬ a < b

_≱_ : Rel ℕ Level.zero
a ≱ b = ¬ a ≥ b

_≯_ : Rel ℕ Level.zero
a ≯ b = ¬ a > b

-- The following, alternative definition of _≤_ is more suitable for
-- well-founded induction (see Induction.Nat).

infix 4 _≤′_ _<′_ _≥′_ _>′_

data _≤′_ (m : ℕ) : ℕ → Set where
  ≤′-refl :                         m ≤′ m
  ≤′-step : ∀ {n} (m≤′n : m ≤′ n) → m ≤′ suc n

_<′_ : Rel ℕ Level.zero
m <′ n = suc m ≤′ n

_≥′_ : Rel ℕ Level.zero
m ≥′ n = n ≤′ m

_>′_ : Rel ℕ Level.zero
m >′ n = n <′ m

------------------------------------------------------------------------
-- A generalisation of the arithmetic operations

fold : {a : Set} → a → (a → a) → ℕ → a
fold z s zero    = z
fold z s (suc n) = s (fold z s n)

module GeneralisedArithmetic {a : Set} (0# : a) (1+ : a → a) where

  add : ℕ → a → a
  add n z = fold z 1+ n

  mul : (+ : a → a → a) → (ℕ → a → a)
  mul _+_ n x = fold 0# (λ s → x + s) n

------------------------------------------------------------------------
-- Arithmetic

pred : ℕ → ℕ
pred zero    = zero
pred (suc n) = n

infixl 6 _+_ _+⋎_

_+_ : ℕ → ℕ → ℕ
zero  + n = n
suc m + n = suc (m + n)

{-# BUILTIN NATPLUS _+_ #-}

-- Argument-swapping addition. Used by Data.Vec._⋎_.

_+⋎_ : ℕ → ℕ → ℕ
zero  +⋎ n = n
suc m +⋎ n = suc (n +⋎ m)

_∸_ : ℕ → ℕ → ℕ
m     ∸ zero  = m
zero  ∸ suc n = zero
suc m ∸ suc n = m ∸ n

{-# BUILTIN NATMINUS _∸_ #-}

_*_ : ℕ → ℕ → ℕ
zero  * n = zero
suc m * n = n + m * n

{-# BUILTIN NATTIMES _*_ #-}

-- Max.

_⊔_ : ℕ → ℕ → ℕ
zero  ⊔ n     = n
suc m ⊔ zero  = suc m
suc m ⊔ suc n = suc (m ⊔ n)

-- Min.

_⊓_ : ℕ → ℕ → ℕ
zero  ⊓ n     = zero
suc m ⊓ zero  = zero
suc m ⊓ suc n = suc (m ⊓ n)

-- Division by 2, rounded downwards.

⌊_/2⌋ : ℕ → ℕ
⌊ 0 /2⌋           = 0
⌊ 1 /2⌋           = 0
⌊ suc (suc n) /2⌋ = suc ⌊ n /2⌋

-- Division by 2, rounded upwards.

⌈_/2⌉ : ℕ → ℕ
⌈ n /2⌉ = ⌊ suc n /2⌋

------------------------------------------------------------------------
-- Queries

infix 4 _≟_

_≟_ : Decidable {A = ℕ} _≡_
zero  ≟ zero   = yes refl
suc m ≟ suc n  with m ≟ n
suc m ≟ suc .m | yes refl = yes refl
suc m ≟ suc n  | no prf   = no (prf ∘ PropEq.cong pred)
zero  ≟ suc n  = no λ()
suc m ≟ zero   = no λ()

≤-pred : ∀ {m n} → suc m ≤ suc n → m ≤ n
≤-pred (s≤s m≤n) = m≤n

_≤?_ : Decidable _≤_
zero  ≤? _     = yes z≤n
suc m ≤? zero  = no λ()
suc m ≤? suc n with m ≤? n
...            | yes m≤n = yes (s≤s m≤n)
...            | no  m≰n = no  (m≰n ∘ ≤-pred)

-- A comparison view. Taken from "View from the left"
-- (McBride/McKinna); details may differ.

data Ordering : Rel ℕ Level.zero where
  less    : ∀ m k → Ordering m (suc (m + k))
  equal   : ∀ m   → Ordering m m
  greater : ∀ m k → Ordering (suc (m + k)) m

compare : ∀ m n → Ordering m n
compare zero    zero    = equal   zero
compare (suc m) zero    = greater zero m
compare zero    (suc n) = less    zero n
compare (suc m) (suc n) with compare m n
compare (suc .m)           (suc .(suc m + k)) | less    m k = less    (suc m) k
compare (suc .m)           (suc .m)           | equal   m   = equal   (suc m)
compare (suc .(suc m + k)) (suc .m)           | greater m k = greater (suc m) k

-- If there is an injection from a set to ℕ, then equality of the set
-- can be decided.

eq? : ∀ {s₁ s₂} {S : Setoid s₁ s₂} →
      Injection S (PropEq.setoid ℕ) → Decidable (Setoid._≈_ S)
eq? inj x y with to ⟨$⟩ x ≟ to ⟨$⟩ y where open Injection inj
... | yes tox≡toy = yes (Injection.injective inj tox≡toy)
... | no  tox≢toy = no  (tox≢toy ∘ F.cong (Injection.to inj))

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

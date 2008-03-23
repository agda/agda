------------------------------------------------------------------------
-- Natural numbers
------------------------------------------------------------------------

module Data.Nat where

open import Data.Function
open import Logic
open import Data.Sum
open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality

infixl 7 _*_ _⊓_
infixl 6 _+_ _∸_ _⊔_
infix  4 _≤_ _<_

------------------------------------------------------------------------
-- The types

data ℕ : Set where
  zero : ℕ
  suc  : ℕ -> ℕ

{-# BUILTIN NATURAL ℕ    #-}
{-# BUILTIN ZERO    zero #-}
{-# BUILTIN SUC     suc  #-}

data _≤_ : ℕ -> ℕ -> Set where
  z≤n : forall {n}            -> zero  ≤ n
  s≤s : forall {m n} -> m ≤ n -> suc m ≤ suc n

_<_ : ℕ -> ℕ -> Set
m < n = suc m ≤ n

------------------------------------------------------------------------
-- A generalisation of the arithmetic operations

fold : {a : Set} -> a -> (a -> a) -> ℕ -> a
fold z s zero    = z
fold z s (suc n) = s (fold z s n)

module GeneralisedArithmetic {a : Set} (0# : a) (1+ : a -> a) where

  add : ℕ -> a -> a
  add n z = fold z 1+ n

  mul : (+ : a -> a -> a) -> (ℕ -> a -> a)
  mul _+_ n x = fold 0# (\s -> s + x) n

------------------------------------------------------------------------
-- Arithmetic

pred : ℕ -> ℕ
pred zero    = zero
pred (suc n) = n

_+_ : ℕ -> ℕ -> ℕ
zero  + n = n
suc m + n = suc (m + n)

{-# BUILTIN NATPLUS _+_ #-}

_∸_ : ℕ -> ℕ -> ℕ
m     ∸ zero  = m
zero  ∸ suc n = zero
suc m ∸ suc n = m ∸ n

{-# BUILTIN NATMINUS _∸_ #-}

_*_ : ℕ -> ℕ -> ℕ
zero  * n = zero
suc m * n = m * n + n

{-# BUILTIN NATTIMES _*_ #-}

_⊔_ : ℕ -> ℕ -> ℕ
zero  ⊔ n     = n
suc m ⊔ zero  = suc m
suc m ⊔ suc n = suc (m ⊔ n)

_⊓_ : ℕ -> ℕ -> ℕ
zero  ⊓ n     = zero
suc m ⊓ zero  = zero
suc m ⊓ suc n = suc (m ⊓ n)

------------------------------------------------------------------------
-- Queries

ℕ-total : Total _≤_
ℕ-total zero    _       = inj₁ z≤n
ℕ-total _       zero    = inj₂ z≤n
ℕ-total (suc m) (suc n) with ℕ-total m n
...                     | inj₁ m≤n = inj₁ (s≤s m≤n)
...                     | inj₂ n≤m = inj₂ (s≤s n≤m)

zero≢suc : forall {n} -> ¬ zero ≡ suc n
zero≢suc ()

_ℕ-≟_ : Decidable {ℕ} _≡_
zero  ℕ-≟ zero   = yes ≡-refl
suc m ℕ-≟ suc n  with m ℕ-≟ n
suc m ℕ-≟ suc .m | yes ≡-refl = yes ≡-refl
suc m ℕ-≟ suc n  | no prf     = no (prf ∘ ≡-cong pred)
zero  ℕ-≟ suc n  = no (⊥-elim ∘ zero≢suc)
suc m ℕ-≟ zero   = no (⊥-elim ∘ zero≢suc ∘ ≡-sym)

suc≰zero : forall {n} -> ¬ suc n ≤ zero
suc≰zero ()

≤-pred : forall {m n} -> suc m ≤ suc n -> m ≤ n
≤-pred (s≤s m≤n) = m≤n

_≤?_ : Decidable _≤_
zero  ≤? _     = yes z≤n
suc m ≤? zero  = no suc≰zero
suc m ≤? suc n with m ≤? n
...            | yes m≤n = yes (s≤s m≤n)
...            | no  m≰n = no  (m≰n ∘ ≤-pred)

-- A comparison view. Taken from "View from the left"
-- (McBride/McKinna); details may differ.

data Ordering : ℕ -> ℕ -> Set where
  less    : forall m k -> Ordering m (suc (m + k))
  equal   : forall m   -> Ordering m m
  greater : forall m k -> Ordering (suc (m + k)) m

compare : forall m n -> Ordering m n
compare zero    zero    = equal   zero
compare (suc m) zero    = greater zero m
compare zero    (suc n) = less    zero n
compare (suc m) (suc n) with compare m n
compare (suc .m)           (suc .(suc m + k)) | less    m k = less    (suc m) k
compare (suc .m)           (suc .m)           | equal   m   = equal   (suc m)
compare (suc .(suc m + k)) (suc .m)           | greater m k = greater (suc m) k

------------------------------------------------------------------------
-- Some properties

ℕ-preorder : Preorder
ℕ-preorder = ≡-preorder ℕ

ℕ-setoid : Setoid
ℕ-setoid = ≡-setoid ℕ

ℕ-decTotalOrder : DecTotalOrder
ℕ-decTotalOrder = record
  { carrier         = ℕ
  ; _≈_             = _≡_
  ; _≤_             = _≤_
  ; isDecTotalOrder = record
      { isTotalOrder = record
          { isPartialOrder = record
              { isPreorder = record
                  { isEquivalence = ≡-isEquivalence
                  ; refl          = refl
                  ; trans         = trans
                  ; ≈-resp-∼      = ≡-resp _≤_
                  }
              ; antisym  = antisym
              }
          ; total = ℕ-total
          }
      ; _≟_  = _ℕ-≟_
      ; _≤?_ = _≤?_
      }
  }
  where
  refl : _≡_ ⇒ _≤_
  refl {zero}  ≡-refl = z≤n
  refl {suc m} ≡-refl = s≤s (refl ≡-refl)

  antisym : Antisymmetric _≡_ _≤_
  antisym z≤n       z≤n       = ≡-refl
  antisym (s≤s m≤n) (s≤s n≤m) with antisym m≤n n≤m
  ...                         | ≡-refl = ≡-refl

  trans : Transitive _≤_
  trans z≤n       _         = z≤n
  trans (s≤s m≤n) (s≤s n≤o) = s≤s (trans m≤n n≤o)

ℕ-decSetoid : DecSetoid
ℕ-decSetoid = DecTotalOrder.Eq.decSetoid ℕ-decTotalOrder

ℕ-poset : Poset
ℕ-poset = DecTotalOrder.poset ℕ-decTotalOrder

import Relation.Binary.PartialOrderReasoning as POR
module ≤-Reasoning = POR ℕ-poset
  renaming (_≈⟨_⟩_ to _≡⟨_⟩_; ≈-byDef to ≡-byDef)

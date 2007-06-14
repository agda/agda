------------------------------------------------------------------------
-- Natural numbers
------------------------------------------------------------------------

module Prelude.Nat where

open import Prelude.Function
open import Prelude.Logic
open import Prelude.Sum
open import Prelude.BinaryRelation
open import Prelude.BinaryRelation.PropositionalEquality

infixl 7 _*_
infixl 6 _+_ _∸_

------------------------------------------------------------------------
-- The types

data ℕ : Set where
  zero : ℕ
  suc  : ℕ -> ℕ

{-# BUILTIN NATURAL ℕ    #-}
{-# BUILTIN ZERO    zero #-}
{-# BUILTIN SUC     suc  #-}

data _ℕ-≤_ : ℕ -> ℕ -> Set where
  z≤n : forall {n}              -> zero  ℕ-≤ n
  s≤s : forall {m n} -> m ℕ-≤ n -> suc m ℕ-≤ suc n

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

------------------------------------------------------------------------
-- Queries

abstract

  ℕ-total : Total _ℕ-≤_
  ℕ-total zero    _       = inj₁ z≤n
  ℕ-total _       zero    = inj₂ z≤n
  ℕ-total (suc m) (suc n) with ℕ-total m n
  ℕ-total (suc m) (suc n) | inj₁ m≤n = inj₁ (s≤s m≤n)
  ℕ-total (suc m) (suc n) | inj₂ n≤m = inj₂ (s≤s n≤m)

  zero≢suc : forall {n} -> ¬ zero ≡ suc n
  zero≢suc ()

  _ℕ-≟_ : Decidable {ℕ} _≡_
  zero  ℕ-≟ zero   = yes ≡-refl
  suc m ℕ-≟ suc n  with m ℕ-≟ n
  suc m ℕ-≟ suc .m | yes ≡-refl = yes ≡-refl
  suc m ℕ-≟ suc n  | no prf     = no (prf ∘ ≡-cong pred)
  zero  ℕ-≟ suc n  = no (⊥-elim ∘ zero≢suc)
  suc m ℕ-≟ zero   = no (⊥-elim ∘ zero≢suc ∘ ≡-sym)

  suc≰zero : forall {n} -> ¬ suc n ℕ-≤ zero
  suc≰zero ()

  ℕ-≤-pred : forall {m n} -> suc m ℕ-≤ suc n -> m ℕ-≤ n
  ℕ-≤-pred (s≤s m≤n) = m≤n

  _ℕ-≤?_ : Decidable _ℕ-≤_
  zero  ℕ-≤? _     = yes z≤n
  suc m ℕ-≤? zero  = no suc≰zero
  suc m ℕ-≤? suc n with m ℕ-≤? n
  suc m ℕ-≤? suc n | yes m≤n = yes (s≤s m≤n)
  suc m ℕ-≤? suc n | no  m≰n = no  (m≰n ∘ ℕ-≤-pred)

------------------------------------------------------------------------
-- Some properties

ℕ-preSetoid : PreSetoid
ℕ-preSetoid = ≡-preSetoid ℕ

ℕ-setoid : Setoid
ℕ-setoid = ≡-setoid ℕ

ℕ-decSetoid : DecSetoid
ℕ-decSetoid = record { setoid = ℕ-setoid; _≟_ = _ℕ-≟_ }

ℕ-partialOrder : PartialOrder _≡_ _ℕ-≤_
ℕ-partialOrder = record
  { equiv    = ≡-equivalence
  ; preorder = record
      { refl  = refl
      ; trans = trans
      }
  ; antisym  = antisym
  ; ≈-resp-≤ = subst⟶resp₂ _ℕ-≤_ ≡-subst
  }
  where
  abstract
    refl : Reflexive _≡_ _ℕ-≤_
    refl {zero}  ≡-refl = z≤n
    refl {suc m} ≡-refl = s≤s (refl ≡-refl)

    antisym : Antisymmetric _≡_ _ℕ-≤_
    antisym z≤n       z≤n       = ≡-refl
    antisym (s≤s m≤n) (s≤s n≤m) with antisym m≤n n≤m
    antisym (s≤s m≤n) (s≤s n≤m) | ≡-refl = ≡-refl

    trans : Transitive _ℕ-≤_
    trans z≤n       _         = z≤n
    trans (s≤s m≤n) (s≤s n≤o) = s≤s (trans m≤n n≤o)

ℕ-poset : Poset
ℕ-poset = record
  { carrier  = ℕ
  ; _≈_      = _≡_
  ; _≤_      = _ℕ-≤_
  ; ord      = ℕ-partialOrder
  }

ℕ-decTotOrder : DecTotOrder
ℕ-decTotOrder = record
  { poset = ℕ-poset
  ; _≟_   = _ℕ-≟_
  ; _≤?_  = _ℕ-≤?_
  ; total = ℕ-total
  }

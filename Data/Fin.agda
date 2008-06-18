------------------------------------------------------------------------
-- Finite sets
------------------------------------------------------------------------

-- Note that elements of Fin n can be seen as natural numbers in the
-- set {m | m < n}. The notation "m" in comments below refers to this
-- natural number view.

module Data.Fin where

open import Data.Nat hiding (zero≢suc)
open import Data.Function
open import Data.Empty
open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Algebra

------------------------------------------------------------------------
-- The type

data Fin : ℕ -> Set where
  zero : {n : ℕ} -> Fin (suc n)
  suc  : {n : ℕ} (i : Fin n) -> Fin (suc n)

------------------------------------------------------------------------
-- Conversion

-- toℕ "n" = n.

toℕ : forall {n} -> Fin n -> ℕ
toℕ zero    = 0
toℕ (suc i) = suc (toℕ i)

-- fromℕ n = "n".

fromℕ : (n : ℕ) -> Fin (suc n)
fromℕ zero    = zero
fromℕ (suc n) = suc (fromℕ n)

------------------------------------------------------------------------
-- Operations

-- raise m "n" = "m + n".

raise : forall {m} n -> Fin m -> Fin (n + m)
raise zero    i = i
raise (suc n) i = suc (raise n i)

-- inject m "n" = "n" (see Data.Fin.Props.inject-lemma).

inject : forall {m} n -> Fin m -> Fin (m + n)
inject n zero    = zero
inject n (suc i) = suc (inject n i)

inject' : forall {m n} -> Fin m -> m ≤ n -> Fin n
inject' zero    (s≤s le) = zero
inject' (suc i) (s≤s le) = suc (inject' i le)

-- n - "m" = n ∸ m.

infixl 6 _-_

_-_ : (n : ℕ) -> Fin (suc n) -> ℕ
m     - zero   = m
zero  - suc ()
suc n - suc i  = n - i

-- addFin "m" "n" = "m + n".

addFin : forall {m n} (i : Fin m) (j : Fin n) -> Fin (toℕ i + n)
addFin zero    j = j
addFin (suc i) j = suc (addFin i j)

------------------------------------------------------------------------
-- Queries

zero≢suc : forall {n} {x : Fin n} ->
           ¬ zero ≡ (Fin (suc n) ∶ suc x)
zero≢suc ()

private
  drop-suc : forall {o} {m n : Fin o} ->
             suc m ≡ (Fin (suc o) ∶ suc n) -> m ≡ n
  drop-suc ≡-refl = ≡-refl

_Fin-≟_ : {n : ℕ} -> Decidable {Fin n} _≡_
zero  Fin-≟ zero   = yes ≡-refl
suc m Fin-≟ suc n  with m Fin-≟ n
suc m Fin-≟ suc .m | yes ≡-refl = yes ≡-refl
suc m Fin-≟ suc n  | no prf     = no (prf ∘ drop-suc)
zero  Fin-≟ suc n  = no (⊥-elim ∘ zero≢suc)
suc m Fin-≟ zero   = no (⊥-elim ∘ zero≢suc ∘ sym)
  where sym = IsEquivalence.sym ≡-isEquivalence

------------------------------------------------------------------------
-- Some properties

Fin-preorder : ℕ -> Preorder
Fin-preorder n = ≡-preorder (Fin n)

Fin-setoid : ℕ -> Setoid
Fin-setoid n = ≡-setoid (Fin n)

Fin-decSetoid : ℕ -> DecSetoid
Fin-decSetoid n = ≡-decSetoid (_Fin-≟_ {n = n})

Fin-bounded : forall {n} (i : Fin n) -> toℕ i < n
Fin-bounded zero    = s≤s z≤n
Fin-bounded (suc i) = s≤s (Fin-bounded i)

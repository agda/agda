------------------------------------------------------------------------
-- Finite sets
------------------------------------------------------------------------

-- Note that elements of Fin n can be seen as natural numbers in the
-- set {m | m < n}. The notation "m" in comments below refers to this
-- natural number view.

module Data.Fin where

open import Data.Nat
open import Logic
open import Data.Function
open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality

infixl 6 _-_

------------------------------------------------------------------------
-- The type

data Fin : ℕ -> Set where
  fz : {n : ℕ} -> Fin (suc n)
  fs : {n : ℕ} -> Fin n -> Fin (suc n)

------------------------------------------------------------------------
-- Conversion

-- toℕ "n" = n.

toℕ : forall {n} -> Fin n -> ℕ
toℕ fz     = 0
toℕ (fs i) = suc (toℕ i)

-- fromℕ n = "n".

fromℕ : (n : ℕ) -> Fin (suc n)
fromℕ zero    = fz
fromℕ (suc n) = fs (fromℕ n)

------------------------------------------------------------------------
-- Operations

-- raise m "n" = "m + n".

raise : forall {n} m -> Fin n -> Fin (m + n)
raise zero    i = i
raise (suc n) i = fs (raise n i)

-- inject m "n" = "n" (see Data.Fin.Props.inject-lemma).

inject : forall {m} n -> Fin m -> Fin (m + n)
inject m fz     = fz
inject m (fs i) = fs (inject m i)

_-_ : (n : ℕ) -> Fin (suc n) -> ℕ
m     - fz    = m
zero  - fs ()
suc n - fs i  = n - i

------------------------------------------------------------------------
-- Queries

fz≢fs : forall {n} {x : Fin n} -> ¬ fz ≡ fs x
fz≢fs ()

private
  drop-fs : forall {o} {m n : Fin o} -> fs m ≡ fs n -> m ≡ n
  drop-fs ≡-refl = ≡-refl

_Fin-≟_ : {n : ℕ} -> Decidable {Fin n} _≡_
fz   Fin-≟ fz    = yes ≡-refl
fs m Fin-≟ fs n  with m Fin-≟ n
fs m Fin-≟ fs .m | yes ≡-refl = yes ≡-refl
fs m Fin-≟ fs n  | no prf     = no (prf ∘ drop-fs)
fz   Fin-≟ fs n  = no (⊥-elim ∘ fz≢fs)
fs m Fin-≟ fz    = no (⊥-elim ∘ fz≢fs ∘ sym)
  where sym = IsEquivalence.sym ≡-isEquivalence

------------------------------------------------------------------------
-- Some properties

Fin-preorder : ℕ -> Preorder
Fin-preorder n = ≡-preorder (Fin n)

Fin-setoid : ℕ -> Setoid
Fin-setoid n = ≡-setoid (Fin n)

Fin-decSetoid : ℕ -> DecSetoid
Fin-decSetoid n = ≡-decSetoid (_Fin-≟_ {n = n})

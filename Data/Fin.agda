------------------------------------------------------------------------
-- Finite sets
------------------------------------------------------------------------

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
-- Operations

raise : forall {n} m -> Fin n -> Fin (m + n)
raise zero    i = i
raise (suc n) i = fs (raise n i)

_-_ : (n : ℕ) -> Fin n -> ℕ
zero  - ()
suc n - fz   = suc n
suc n - fs i = n - i

------------------------------------------------------------------------
-- Queries

abstract

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
    where sym = Equivalence.sym ≡-equivalence

------------------------------------------------------------------------
-- Some properties

Fin-preSetoid : ℕ -> PreSetoid
Fin-preSetoid n = ≡-preSetoid (Fin n)

Fin-setoid : ℕ -> Setoid
Fin-setoid n = ≡-setoid (Fin n)

Fin-decSetoid : ℕ -> DecSetoid
Fin-decSetoid n = record { setoid = Fin-setoid n; _≟_ = _Fin-≟_ }

------------------------------------------------------------------------
-- Properties related to Fin, and operations making use of these
-- properties
------------------------------------------------------------------------

module Data.Fin.Props where

open import Data.Fin
open import Data.Nat
open import Data.Nat.Properties
open import Relation.Binary
open import Relation.Binary.PropositionalEquality

------------------------------------------------------------------------
-- Properties

prop-toℕ-≤ : forall {n} (x : Fin n) -> toℕ x ≤ pred n
prop-toℕ-≤ zero                 = z≤n
prop-toℕ-≤ (suc {n = zero}  ())
prop-toℕ-≤ (suc {n = suc n} i)  = s≤s (prop-toℕ-≤ i)

inject-lemma : forall m k -> m ≡ toℕ (inject k (fromℕ m))
inject-lemma zero    k = ≡-refl
inject-lemma (suc m) k = ≡-cong suc (inject-lemma m k)

------------------------------------------------------------------------
-- Operations

addFin' : forall {m n} (i : Fin m) (j : Fin n) -> Fin (pred m + n)
addFin' i j = inject' (addFin i j) (prop-toℕ-≤ i +-mono refl)
  where open Poset ℕ-poset

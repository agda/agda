------------------------------------------------------------------------
-- Properties related to Fin
------------------------------------------------------------------------

module Data.Fin.Props where

open import Data.Fin
open import Data.Nat
open import Relation.Binary.PropositionalEquality

prop-toℕ-≤ : forall {n} (x : Fin n) -> toℕ x ≤ n
prop-toℕ-≤ fz     = z≤n
prop-toℕ-≤ (fs i) = s≤s (prop-toℕ-≤ i)

inject-lemma : forall m k -> m ≡ toℕ (inject k (fromℕ m))
inject-lemma zero    k = ≡-refl
inject-lemma (suc m) k = ≡-cong suc (inject-lemma m k)

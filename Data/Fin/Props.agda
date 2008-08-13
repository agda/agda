------------------------------------------------------------------------
-- Properties related to Fin, and operations making use of these
-- properties (or other properties not available in Data.Fin)
------------------------------------------------------------------------

module Data.Fin.Props where

open import Data.Fin
import Data.Nat as Nat
open Nat using (ℕ; zero; suc; _≤_; z≤n; s≤s)
         renaming (_+_ to _ℕ+_)
open Nat.≤-Reasoning
open import Data.Nat.Properties
open import Relation.Binary
open import Relation.Binary.PropositionalEquality

------------------------------------------------------------------------
-- Properties

prop-toℕ-≤ : forall {n} (x : Fin n) -> toℕ x ≤ Nat.pred n
prop-toℕ-≤ zero                 = z≤n
prop-toℕ-≤ (suc {n = zero}  ())
prop-toℕ-≤ (suc {n = suc n} i)  = s≤s (prop-toℕ-≤ i)

nℕ-ℕi≤n : forall n i -> n ℕ-ℕ i ≤ n
nℕ-ℕi≤n n       zero     = begin n ∎
nℕ-ℕi≤n zero    (suc ())
nℕ-ℕi≤n (suc n) (suc i)  = begin
  n ℕ-ℕ i ≤⟨ nℕ-ℕi≤n n i ⟩
  n       ≤⟨ n≤1+n n ⟩
  suc n   ∎

inject+-lemma : forall m k -> m ≡ toℕ (inject+ k (fromℕ m))
inject+-lemma zero    k = ≡-refl
inject+-lemma (suc m) k = ≡-cong suc (inject+-lemma m k)

------------------------------------------------------------------------
-- Operations

infixl 6 _+′_

_+′_ : forall {m n} (i : Fin m) (j : Fin n) -> Fin (Nat.pred m ℕ+ n)
i +′ j = inject≤ (i + j) (prop-toℕ-≤ i +-mono refl)
  where open Poset Nat.ℕ-poset

-- reverse {n} "i" = "n ∸ 1 ∸ i".

reverse : forall {n} -> Fin n -> Fin n
reverse {zero}  ()
reverse {suc n} i  = inject≤ (n ℕ- i) (n∸m≤n (toℕ i) (suc n))

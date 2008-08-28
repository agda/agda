------------------------------------------------------------------------
-- Natural numbers with fast addition (for use together with
-- DifferenceVec)
------------------------------------------------------------------------

module Data.DifferenceNat where

import Data.Nat as N
open N using (ℕ)
open import Data.Function

infixl 6 _+_

Diffℕ : Set
Diffℕ = ℕ -> ℕ

0# : Diffℕ
0# = \k -> k

suc : Diffℕ -> Diffℕ
suc n = \k -> N.suc (n k)

1# : Diffℕ
1# = suc 0#

_+_ : Diffℕ -> Diffℕ -> Diffℕ
m + n = \k -> m (n k)

toℕ : Diffℕ -> ℕ
toℕ n = n 0

-- fromℕ n is linear in the size of n.

fromℕ : ℕ -> Diffℕ
fromℕ n = \k -> n ⟨ N._+_ ⟩ k

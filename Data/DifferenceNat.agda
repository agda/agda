------------------------------------------------------------------------
-- Natural numbers with fast addition (for use together with
-- DifferenceVec)
------------------------------------------------------------------------

module Data.DifferenceNat where

open import Data.Nat as N using (ℕ)
open import Data.Function

infixl 6 _+_

Diffℕ : Set
Diffℕ = ℕ → ℕ

0# : Diffℕ
0# = λ k → k

suc : Diffℕ → Diffℕ
suc n = λ k → N.suc (n k)

1# : Diffℕ
1# = suc 0#

_+_ : Diffℕ → Diffℕ → Diffℕ
m + n = λ k → m (n k)

toℕ : Diffℕ → ℕ
toℕ n = n 0

-- fromℕ n is linear in the size of n.

fromℕ : ℕ → Diffℕ
fromℕ n = λ k → n ⟨ N._+_ ⟩ k

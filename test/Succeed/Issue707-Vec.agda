-- Andreas, 2016-07-29 issue #707, comment of 2012-10-31

open import Common.Nat

data Vec (A : Set) : Nat → Set where
  []  : Vec A zero
  _∷_ : ∀ {n} (x : A) (xs : Vec A n) → Vec A (suc n)

v0 v1 v2 : Vec Nat _
v0 = []
v1 = 0 ∷ v0
v2 = 1 ∷ v1

-- Works, but maybe questionable.
-- The _ is triplicated into three different internal metas.

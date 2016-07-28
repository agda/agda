-- Andreas, 2016-07-28 issue 2120, reported by guillaume

-- {-# OPTIONS -v tc.term.exlam:50 #-}

open import Common.Product

data Nat : Set where
  zero : Nat

data Eq {A : Set}(a : A) : A → Set where
  refl : Eq a a

postulate _<∣_ : ∀ {X Y : Set} → (X → Y) → X → Y

test : Nat
test = ( λ { (zero , refl) → zero } ) <∣ (zero , zero)

-- WAS: Internal error in Reduce

-- EXPECTED: Proper error, like
--
-- Type mismatch
-- when checking that the pattern refl has type _15 zero

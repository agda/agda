-- Andreas, 2015-05-01
-- With clauses for functions with flexible arity.

-- {-# OPTIONS -v tc.with:40 #-}

open import Common.Prelude
open import Common.Equality

mutual
  even : Nat → Bool
  even 0       = true
  even (suc n) = odd n

  odd  : Nat → Bool
  odd 0 = false
  odd (suc n) = even n

NPred : Nat → Set
NPred 0       = Bool
NPred (suc n) = Nat → NPred n

const : Bool → ∀{n} → NPred n
const b {0}       = b
const b {suc n} m = const b {n}

allOdd : ∀ n → NPred n
allOdd 0 = true
allOdd (suc n) m with even m
... | true  = const false
... | false = allOdd n

test : allOdd 4 1 3 5 7 ≡ true
test = refl

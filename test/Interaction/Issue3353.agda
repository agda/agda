-- Andreas, 2018-11-23, 2019-07-22, issue #3353
--
-- Preserved names of named arguments under case splitting.

-- {-# OPTIONS -v tc.lhs:40 #-}
-- {-# OPTIONS -v interaction.case:60 -v reify:30 #-}

open import Agda.Builtin.Nat

test : {m n : Nat} → Nat
test {m} {n = n} = {!n!}  -- C-c C-c

-- Splitting on n gives:
-- test {m} {zero} = {!!}
-- test {m} {suc n} = {!!}

-- Expected:
-- test {m} {n = zero} = {!!}
-- test {m} {n = suc n} = {!!}

data Vec (A : Set) : Nat → Set where
  _∷_ : ∀{n} (x : A) (xs : Vec A n) → Vec A (suc n)

foo : ∀{A n} → Vec A n → Vec A n
foo (_∷_ {n = n} x xs) = {!n!}  -- C-c C-c

-- Expected:
-- foo (_∷_ {n = suc n} x xs) = {!!}

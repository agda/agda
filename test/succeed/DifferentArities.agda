
module DifferentArities where

open import Common.Equality
open import Common.Prelude

f : Nat → Nat → Nat
f zero      = λ x → x
f (suc n) m = f n (suc m)

testf1 : f zero ≡ λ x → x
testf1 = refl

testf2 : ∀ {n m} → f (suc n) m ≡ f n (suc m)
testf2 = refl

testf3 : f 4 5 ≡ 9
testf3 = refl

-- Andreas, 2015-01-21 proper matching on additional argument

Sum : Nat → Set
Sum 0       = Nat
Sum (suc n) = Nat → Sum n

sum : (acc : Nat) (n : Nat) → Sum n
sum acc 0         = acc
sum acc (suc n) 0 = sum acc n
sum acc (suc n) m = sum (m + acc) n

nzero : (n : Nat) → Sum n
nzero 0 = 0
nzero (suc n) m = nzero n

mult :  (acc : Nat) (n : Nat) → Sum n
mult acc 0         = acc
mult acc (suc n) 0 = nzero n
mult acc (suc n) m = mult (m * acc) n

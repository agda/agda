
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

open import Common.Prelude
open import TestHarness
open import TestBool using ( not; _∧_ ; _↔_ )

module TestNat where

_*_ : Nat → Nat → Nat
zero  * n = zero
suc m * n = n + (m * n)

{-# COMPILED_JS _*_ function (x) { return function (y) { return x*y; }; } #-}

fact : Nat → Nat
fact zero    = 1
fact (suc x) = suc x * fact x

_≟_ : Nat → Nat → Bool
zero  ≟ zero  = true
suc x ≟ suc y = x ≟ y
x     ≟ y     = false

{-# COMPILED_JS _≟_ function (x) { return function (y) { return x === y; }; } #-}

tests : Tests
tests _ = (
    assert (0 ≟ 0) "0=0" ,
    assert (not (0 ≟ 1)) "0≠1" ,
    assert ((1 + 2) ≟ 3) "1+2=3" ,
    assert ((2 ∸ 1) ≟ 1) "2∸1=1" ,
    assert ((1 ∸ 2) ≟ 0) "1∸2=0" ,
    assert ((2 * 3) ≟ 6) "2+3=6" ,
    assert (fact 0 ≟ 1) "0!=1" ,
    assert (fact 1 ≟ 1) "1!=1" ,
    assert (fact 2 ≟ 2) "2!=2" ,
    assert (fact 3 ≟ 6) "3!=6" ,
    assert (fact 4 ≟ 24) "4!=24"
  )

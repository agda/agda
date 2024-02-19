
module _ (A : Set) where

open import Agda.Builtin.Nat
open import Agda.Builtin.Equality

data D : Set where
  foo : Nat → Nat → D

record R : Set where
  constructor mkR
  field n : Nat

postulate
  P : Set
  mkP : Nat → P

testD : Nat → D
testD n = {!!}

testR : Nat → R
testR n = {!!}

testP : Nat → P
testP n = {!!}

testRefined : (B C : Set) → A ≡ (B → C) → Nat → D
testRefined B C refl n = {!!}

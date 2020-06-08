{-# OPTIONS --cubical #-}
module PathWith where

open import Agda.Builtin.Cubical.Path
open import Agda.Primitive.Cubical
open import Agda.Builtin.Nat

pred : Nat → Nat
pred (suc n) = n
pred 0 = 0

f : Nat → Nat
f n with pred n
... | zero = zero
... | suc m = suc m

module _ (qqq : Nat) where

  test1 : f ≡ pred
  test1 i n with pred n
  ... | zero = zero
  ... | suc q = suc q


test2 : test1 ≡ test1
test2 i n j x with pred x
... | zero = zero
... | suc q = suc q

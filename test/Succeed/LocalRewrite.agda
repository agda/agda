{-# OPTIONS --rewriting #-}

open import Agda.Builtin.Nat
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite

f : Nat → Nat
f zero    = zero
f (suc n) = suc (suc (f n))

module Foo (x : Nat) (@rew p : f x ≡ 0) where
  test : f x ≡ 0
  test = refl

test2 : f 0 ≡ 0
test2 = Foo.test 0 refl

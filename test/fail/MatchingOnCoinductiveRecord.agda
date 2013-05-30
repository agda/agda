{-# OPTIONS --copatterns #-}
-- 2013-05-30 Andreas, Oury's counterexample to subject reduction in Coq
module MatchingOnCoinductiveRecord where

open import Common.Equality

record U : Set where
  coinductive
  constructor inn
  field
    out : U
open U

u : U
out u = u

-- should fail:
force : U → U
force (inn y) = inn y

eq : (x : U) → x ≡ force x
eq (inn y) = refl

equ : u ≡ inn u
equ = eq u
-- normalizes to refl, which does not have type u ≡ inn u


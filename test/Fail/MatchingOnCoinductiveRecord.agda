{-# OPTIONS --guardedness #-}

-- 2013-05-30 Andreas, Oury's counterexample to subject reduction in Coq
-- 2014-11-04 Andreas: simplified (removed force)

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

eq : (x : U) → x ≡ inn (out x)
eq (inn y) = refl
-- should fail, as internally this is just
-- eq x = refl
-- and we do not have η for coinductive records

equ : u ≡ inn u
equ = eq u
-- normalizes to refl, which does not have type u ≡ inn u

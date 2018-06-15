-- Andreas, 2018-06-10, issue #2797
-- Analysis and test case by Ulf

-- Relevance check was missing for overloaded projections.

{-# OPTIONS --irrelevant-projections #-}

-- {-# OPTIONS -v tc.proj.amb:30 #-}

open import Agda.Builtin.Nat

record Dummy : Set₁ where
  field nat : Set
open Dummy

record S : Set where
  field .nat : Nat
open S

mkS : Nat → S
mkS n .nat = n

-- The following should not pass, as projection
-- .nat is irrelevant for record type S

unS : S → Nat
unS s = s .nat

-- Error NOW, could be better:
-- Cannot resolve overloaded projection nat because no matching candidate found
-- when checking that the expression s .nat has type Nat

viaS : Nat → Nat
viaS n = unS (mkS n)

idN : Nat → Nat
idN zero    = zero
idN (suc n) = suc n

canonicity-fail : Nat
canonicity-fail = idN (viaS 17)
-- C-c C-n canonicity-fail
-- idN .(17)

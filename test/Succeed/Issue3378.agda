-- Andrea(s), 2018-11-23, issue #3378
--
-- WAS: internal error in coverage checker and clause compiler
-- for missing hcomp clauses triggered by non-exact splitting.

{-# OPTIONS --cubical #-}

-- {-# OPTIONS -v tc.cover:10 #-}

open import Agda.Builtin.Cubical.Path
open import Agda.Builtin.Unit

data Interval : Set where
  pos : Interval
  neg : Interval
  zeroes-identified : pos ≡ neg

test : Interval → Interval → ⊤
test pos pos = tt
test neg pos = tt
test (zeroes-identified i) pos = tt
test x neg = tt
test x (zeroes-identified j) = tt

-- Should pass (with non-exact splitting).

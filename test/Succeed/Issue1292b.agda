-- Andreas, 2014-10-05

{-# OPTIONS --cubical-compatible --sized-types #-}

-- {-# OPTIONS -v tc.size:20  #-}

open import Agda.Builtin.Size

data Nat : {size : Size} -> Set where
  zero : {size : Size} -> Nat {↑ size}
  suc  : {size : Size} -> Nat {size} -> Nat {↑ size}

-- subtraction is non size increasing
sub : {size : Size} -> Nat {size} -> Nat {∞} -> Nat {size}
sub zero    n       = zero
sub (suc m) zero    = suc m
sub (suc m) (suc n) = sub m n

-- div' m n  computes  ceiling(m/(n+1))
div' : {size : Size} -> Nat {size} -> Nat -> Nat {size}
div' zero    n = zero
div' (suc m) n = suc (div' (sub m n) n)

-- should termination check even --cubical-compatible

-- -}

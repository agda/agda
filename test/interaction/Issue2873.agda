-- Andreas, 2017-12-16, issue #2873, reported by m0davis

-- Regression introduced by a fix of #737 that printed
-- the refinement candidate to concrete syntax
-- and ran the scope checker again to get back to abstract syntax.

-- {-# OPTIONS -v interaction:50 #-}

open import Agda.Builtin.Nat

data Vec {a} (A : Set a) : Nat → Set a where
  []  : Vec A zero
  _∷_ : ∀ {n} (x : A) (xs : Vec A n) → Vec A (suc n)

module Fails where
  open import Agda.Builtin.List

  test : Vec Nat 1
  test = {!(_∷_) !} -- WAS: C-c C-r fails here

  test2 : Vec Nat 1
  test2 = {! !} -- WAS: C-c C-r fails here

module Succeeds where
  open import Agda.Builtin.List public

  test : Vec Nat 1
  test = {!!} -- C-c C-r succeeds here

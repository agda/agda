-- Partly based on code due to Andrea Vezzosi.

{-# OPTIONS --without-K --safe #-}

open import Agda.Builtin.Bool

data D : Set where
  run-time        : Bool → D
  @0 compile-time : Bool → D

l : @0 D → D
l (run-time true)  = run-time true
l (run-time false) = run-time false
l (compile-time x) = compile-time x

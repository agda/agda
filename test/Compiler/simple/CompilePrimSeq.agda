{-# OPTIONS -v treeless.opt.builtin:30 -v 0 #-}

module CompilePrimSeq where

open import Agda.Builtin.Nat using (Nat; _+_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Strict using (primForce)

sum : Nat → List Nat → Nat
sum acc []       = acc
sum acc (x ∷ xs) = sum (primForce x _+_ acc) xs

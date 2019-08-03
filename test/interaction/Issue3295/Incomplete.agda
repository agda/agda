{-# OPTIONS --allow-incomplete-match #-}

module Issue3295.Incomplete where

open import Agda.Builtin.Nat

f : Nat → Nat
f zero = zero

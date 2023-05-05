-- Everything in this module is erased.

{-# OPTIONS --erasure #-}

module @0 Erased-modules-1 where

open import Agda.Builtin.Bool

@ω not : @0 Bool → Bool
not true  = false
not false = true

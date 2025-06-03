module Nat1 where

open import Agda.Builtin.Nat              public
open import Agda.Builtin.Equality         public
open import Agda.Builtin.Equality.Rewrite public

n+0 : (n : Nat) → n + 0 ≡ n
n+0 zero = refl
n+0 (suc n) rewrite n+0 n = refl

{-# REWRITE n+0 #-}

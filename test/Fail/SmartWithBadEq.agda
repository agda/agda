{-# OPTIONS --smart-with #-}

open import Agda.Builtin.Bool
open import Agda.Builtin.Nat
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite

f : Nat
f with true
f | true  = {!!}
f | false = {!!}
  where eq : true ≡ false
        eq = refl

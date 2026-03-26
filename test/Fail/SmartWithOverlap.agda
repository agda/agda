{-# OPTIONS --smart-with #-}

open import Agda.Builtin.Bool
open import Agda.Builtin.Nat
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite

not : Bool → Bool
not true  = false
not false = true

f : Bool → Nat
f b with not (not b)
f b | false = 42
f b | true with not b
f b | true | true  = 42
  where bad : true ≡ false
        bad = refl
f b | true | false = 42

{-# OPTIONS --smart-with #-}

open import Agda.Builtin.Bool
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite

not : Bool → Bool
not true  = false
not false = true

foo : (b : Bool) → true ≡ not b → not true ≡ not (not b)
foo b p rewrite p = refl

{-
The rewrite rule 'true ≡ b' should not be accepted (and throw a warning) or
we would get a failure of transitivity of conversion (and therefore subject
reduction).
-}

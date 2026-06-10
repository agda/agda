{-# OPTIONS --rewriting --smart-with #-}

open import Agda.Builtin.Nat
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite

variable
  n : Nat

postulate
  ze+ : n + zero ≡ n
  {-# REWRITE ze+ #-}

foo : (n : Nat) (f : Nat → Nat) → _+_ n ≡ f → n + zero ≡ f zero
foo n f p rewrite p = {!!}

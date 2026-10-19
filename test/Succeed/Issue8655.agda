{-# OPTIONS --rewriting #-}

open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite
open import Agda.Builtin.Sigma

variable
  A : Set
  x : A

abstract
  to : A → A
  to x = x

  from : A → A
  from x = x

  to-from : to (from x) ≡ x
  to-from = refl

{-# REWRITE to-from #-}

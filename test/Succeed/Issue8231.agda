{-# OPTIONS --rewriting #-}

open import Agda.Builtin.Bool
open import Agda.Builtin.Equality
import Agda.Builtin.Equality.Rewrite

postulate
  A : Set
  x : A
  f : .Bool → A
  eq : f false ≡ x

{-# REWRITE eq #-}

bug : f true ≡ x
bug = refl

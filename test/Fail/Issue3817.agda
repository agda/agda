{-# OPTIONS --rewriting --confluence-check #-}

open import Agda.Primitive
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite

postulate
  A : Set
  a b : A
  f : Level → A
  g h : Level
  f-g : f (lsuc g) ≡ a
  f-h : f (lsuc h) ≡ b
  g-h : g ≡ h

{-# REWRITE f-g f-h g-h #-}

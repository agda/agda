{-# OPTIONS --safe --without-K #-}

-- Issue #8704, variant with opaque.
-- See comments in Issue8704-abstract.agda.

open import Agda.Builtin.Bool
open import Agda.Builtin.Equality

dummy : Bool
dummy = true where
  opaque
    hh : Bool
    hh = true

  opaque
    vv : hh ≡ true
    vv = _ -- refl

  opaque
    unfolding hh vv

    Solve : Set
    Solve = vv ≡ refl

    solve : Solve
    solve = refl


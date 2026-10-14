{-# OPTIONS --safe --without-K #-}

-- Issue #8828, variant with opaque.
-- See comments in Issue8828-abstract.agda.

open import Agda.Builtin.Bool
open import Agda.Builtin.Equality

-- Non-unique solution

dummy1 : Bool
dummy1 = true where
  opaque
    secret' : Bool
    secret' = false

  opaque
    Test' : Set
    Test' = secret' ≡ _

  opaque
    unfolding secret' Test'

    test' : Test'
    test' = refl

-- Ill-typed solution

dummy2 : Bool
dummy2 = true where
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

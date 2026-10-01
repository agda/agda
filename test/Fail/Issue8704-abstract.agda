{-# OPTIONS --safe --without-K #-}

open import Agda.Builtin.Bool
open import Agda.Builtin.Equality

mutual
  abstract
    secret : Bool
    secret = false

  Test : Set
  Test = secret ≡ _

  abstract
    test : Test
    test = refl

mutual
  abstract
    hh : Bool
    hh = true

  vv : hh ≡ true
  vv = _ -- refl

  abstract
    Solve : Set
    Solve = vv ≡ refl

    solve : Solve
    solve = refl


{-# OPTIONS --cubical #-}

module Issue4763 where

open import Agda.Builtin.Cubical.Path
open import Agda.Builtin.Reflection
open import Agda.Builtin.Unit

record A : Set₀ where
  constructor mk
  field
    out : ⊤

test : mk tt ≡ mk tt
test = λ where i .A.out → tt

macro
  mac : Term → Term → TC _
  mac t goal =
    bindTC (normalise t) λ norm →
    bindTC {A = mk tt ≡ mk tt} (unquoteTC norm) λ tm →
    unify goal (quoteTerm tt)

_ = mac test

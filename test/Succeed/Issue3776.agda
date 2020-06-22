{-# OPTIONS --allow-unsolved-metas #-}

open import Agda.Builtin.Unit
open import Agda.Builtin.Equality

data Unit : Set where unit : Unit

A : Unit → Set
A unit = ⊤

postulate
  a b : (u : Unit) → A u

mutual
  _X : Unit
  _X = {!unit!}

  test : a _X ≡ b _X
  test = refl

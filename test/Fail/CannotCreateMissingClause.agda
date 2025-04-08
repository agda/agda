{-# OPTIONS --cubical --prop #-}
module CannotCreateMissingClause where

open import Agda.Builtin.Cubical.Path
open import Agda.Primitive.Cubical
open import Agda.Primitive

data S¹ : Set where
  base : S¹
  loop : base ≡ base

test : (P : Prop) → S¹ → P → P
test P base x = x
test P (loop i) x = x

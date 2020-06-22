{-# OPTIONS --cubical #-}
module _ where

open import Agda.Primitive.Cubical
open import Agda.Builtin.Cubical.Path

data ⊤ : Set where
  tt : ⊤

data S : Set where
  base : S
  loop : base ≡ base

postulate
  P' : base ≡ base → Set
  pl : P' loop

foo : P' loop
foo with tt
... | w = pl

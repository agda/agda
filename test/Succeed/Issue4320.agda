{-# OPTIONS --cubical --safe #-}
open import Agda.Builtin.Cubical.Path

data Circle1 : Set where
  base1 : Circle1
  loop : base1 ≡ base1

data Circle2 : Set where
  base2 : Circle2
  loop : base2 ≡ base2

test : base2 ≡ base2
test = loop

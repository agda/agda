{-# OPTIONS --cubical #-}
module Issue8161b where

open import Agda.Builtin.Cubical.Path
open import Agda.Primitive
open import Agda.Primitive.Cubical

variable
  a : Level
  A : Set a
  x : A

refl : x ≡ x
refl {x = x} = λ _ → x

lemma : primTransp (λ i → refl i) i0 x ≡ x
lemma = ?

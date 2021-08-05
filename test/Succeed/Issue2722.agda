{-# OPTIONS --cubical #-}

open import Agda.Primitive.Cubical
open import Agda.Builtin.Cubical.Path

postulate
  A : Set
  B : Set
  b : B

f : (\ {a : A} (x : B) → b) ≡ (\ _ → b)
f i x = b

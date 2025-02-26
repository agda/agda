-- This would fail without the --cubical in the agda-lib file.
module A where

open import Agda.Builtin.Cubical.Path
open import Agda.Primitive
open import Agda.Primitive.Cubical

data Circle : Set where
  zero : Circle
  loop : zero ≡ zero

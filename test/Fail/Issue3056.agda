
open import Agda.Builtin.Unit
open import Agda.Builtin.Bool
open import Agda.Builtin.Sigma

data ⊥ : Set where

type : Bool → Set
type true = ⊤
type false = ⊥

record Bad : Set where
  constructor b
  field
    .f : Σ Bool type

test : Bad → Bool
test (b (x , y)) = x

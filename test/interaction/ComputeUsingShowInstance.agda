
module _ where

open import Agda.Builtin.String

_&_ = primStringAppend

record Show (A : Set) : Set where
  field
    show : A → String

open Show {{...}} public

data Bin : Set where
  []  : Bin
  0:_ : Bin → Bin
  1:_ : Bin → Bin

five : Bin
five = 1: 0: 1: []

instance
  ShowBin : Show Bin
  show {{ShowBin}} [] = ""
  show {{ShowBin}} (0: b) = "0" & show b
  show {{ShowBin}} (1: b) = "1" & show b

hole : Bin → Bin
hole x = {!!}

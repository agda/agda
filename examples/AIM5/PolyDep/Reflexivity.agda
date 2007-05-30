module Reflexivity where
import PolyDepPrelude
open PolyDepPrelude using(Bool; True)

-- Local reflexivity

lref : {X : Set} -> (X -> X -> Bool) -> X -> Set
lref _R_ = \x -> True (x R x)

-- Reflexive = locally reflexive everywhere

data Refl {X : Set} (r : X -> X -> Bool) : Set where
  refl : ((x : X) -> lref r x) -> Refl r

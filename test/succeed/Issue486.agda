
module Issue486 where

record ⊤ : Set where
  constructor tt
 
record Pub (A : Set) : Set where
  field
    fi : A

abstract
  abs : ⊤
  abs = fi
    where open Pub record {fi = tt}

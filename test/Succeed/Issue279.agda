
module Issue279 where

record Unit : Set where
  constructor tt

open Unit tt  -- this no longer brings tt into scope

test : Unit
test = tt

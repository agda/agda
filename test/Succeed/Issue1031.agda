
data Bool : Set where
  true false : Bool

record Top : Set where

foo : Top
foo with true
... | true  = _
... | false = top
  where
    top = record{ }  -- the only purpose of this was to force
                     -- evaluation of the with function clauses
                     -- which were in an __IMPOSSIBLE__ state

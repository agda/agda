
module Issue435 where

data Bool : Set where
  true false : Bool

record Unit : Set where

postulate D : ({x : Bool} -> Bool) -> Set

fails : Set
fails = D (\ { {true}  → false ; {false} → true})

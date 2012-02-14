-- Andreas, 2012-02-14, issue reported by Wolfram Kahl
-- {-# OPTIONS -v scope.top:10 #-}
module Issue562 where

data Bool : Set where true false : Bool

f : Bool → Bool
f b with b
f true | _ = b
-- WAS: panic unbound variable b
-- should be:  Not in scope: b
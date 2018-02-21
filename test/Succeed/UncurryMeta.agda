-- It would be nice if this worked. The constraint we can't solve is
--   P x y = ? (x, y)
-- Solution: extend the notion of Miller patterns to include record
-- constructions.
--
-- Andreas, 2012-02-27 works now! (see issues 376 and 456)
module UncurryMeta where

data Unit : Set where
  unit : Unit

record R : Set where
  constructor _,_
  field
    x : Unit
    y : Unit

data P : Unit -> Unit -> Set where
  mkP : forall x y -> P x y

data D : (R -> Set) -> Set1 where
  d : {F : R -> Set} -> (forall x y -> F (x , y)) -> D F

unD : {F : R -> Set} -> D F -> Unit
unD (d _) = unit

test : Unit
test = unD (d mkP)

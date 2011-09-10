-- 2010-10-04
-- termination checker no longer counts stripping off a record constructor
-- as decrease
module Issue334 where

data Unit : Set where
  unit : Unit

record E : Set where
  constructor mkE
  field
    fromE : E
    spam  : Unit

f : E -> Set
f (mkE e unit) = f e
-- the record pattern translation does not apply to f
-- still, should not termination check, because
--   f (mkE e u) = f e
-- also does not!


-- 2010-10-04
-- termination checker no longer counts stripping off a record constructor
-- as decrease
-- 2019-10-18
-- It does if it's an inductive non-eta record.
module Issue334b where

data Unit : Set where
  unit : Unit

record E : Set where
  inductive
  constructor mkE
  field
    fromE : E
    spam  : Unit

f : E -> Set
f (mkE e unit) = f e

f' : E -> Set
f' (mkE e u) = f e

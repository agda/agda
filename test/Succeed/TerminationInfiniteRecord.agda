-- 2010-10-02, see issue 334

module TerminationInfiniteRecord where

record Empty : Set where
  inductive
  constructor empty
  field
    fromEmpty : Empty

elimEmpty : Empty -> Set
elimEmpty (empty e) = elimEmpty e

-- this no longer termination checks
-- and it should not, since it is translated to
-- elimEmpty e' = elimEmpty (fromEmpty e')

-- UPDATE: it is not translated to that, so it's ok for
-- it to termination check.

module Issue282 where

module Works where

  record R : Set where
    constructor c

  -- foo = R.c  -- Andreas, 2019-11-11, #4189, no more qualified record constructors

module Doesn't_work where

  private

    record R : Set where
      constructor c

  -- foo = R.c  -- Andreas, 2019-11-11, #4189, no more qualified record constructors

-- Bug.agda:17,9-12
-- Not in scope:
--   R.c at Bug.agda:17,9-12
-- when scope checking R.c

module Doesn't_work_either where

  private

    data D : Set where
      c : D

  foo = D.c

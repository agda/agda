
module Issue62 where

module A where

  data A : Set where
    a : A

module B where

  open A

  data B : Set where
    a : B

open B

-- Note that a : A.A is not in scope here, so the following should not
-- type check.

foo : A.A -> A.A
foo a = a

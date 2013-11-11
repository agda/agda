module WrongNamedArgument2 where

postulate
  f : {A : Set₁} → A

test : Set
test = f {B = Set}

-- Unsolved meta.
-- It is not an error since A could be instantiated to a function type
-- accepting hidden argument with name B.

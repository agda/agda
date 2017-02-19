-- Andreas, 2017-02-15, issue #2462
-- Overloaded postfix projection should resolve

postulate
  A : Set

record R : Set where
  constructor mkR
  field f : A
open R

record S : Set where
  field f : R
open S

test : S → A
test s = let mkR x = s .f in x

-- Error WAS:
-- Cannot resolve overloaded projection f because it is not applied to
-- a visible argument
-- when inferring the type of .f

-- {-# OPTIONS -v tc.check.app:70 #-}
-- {-# OPTIONS -v tc.proj.amb:30 #-}

record S : Set₁ where
  field X : Set

record T : Set₁ where
  field X : Set

open S
open T

ok : S → Set
ok s = X s

test : S → Set
test s = s .X

-- Error WAS:
-- Cannot resolve overloaded projection X because it is not applied to
-- a visible argument
-- when inferring the type of .X

-- Should succeed.

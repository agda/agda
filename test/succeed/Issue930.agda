-- {-# OPTIONS -v tc.conv.level:60 #-}
-- {-# OPTIONS -v tc.conv:30 #-}

{- Agda development version: Wed Oct 30 16:30:06 GMT 2013

   The last line of code triggers the following error,
   but replacing '_' with 'a' typechecks just fine.

   Bug.agda:32,8-11
   tt != a of type ⊤
   when checking that the expression s _ has type P tt → P a

   Changing 'Set (q a)' to 'Set' in line 26 suppresses the error.
-}

-- Andreas, 2013-10-31  Fixed by retrying sort comparison after
-- successful type comparison (which might have solve the missing level metas).

module Issue930 where

open import Common.Level

data ⊤ : Set where
  tt : ⊤

postulate
  q : ⊤ → Level
  P : (a : ⊤) → Set (q a)
  s : (a : ⊤) → P tt → P a
  a : ⊤
  g : (P tt → P a) → ⊤

v : ⊤
v = g (s _)

{-
coerce term      v  = s ?1
       from type t1 = P tt → P ?1
       to type   t2 = P tt → P a
equalSort
  Set (q tt ⊔ q ?1) == Set (q a ⊔ q tt)
compareAtom q tt == q a : Level
compareTerm tt == a : ⊤
sort comparison failed  -- THIS ERROR IS CAUGHT, BUT RETHROWN AT THE END
compareTerm P tt → P ?1 =< P tt → P a : Set (q tt ⊔ q ?1)
compare function types
  t1 = P tt → P ?1
  t2 = P tt → P a
equalSort
  Set (q ?1) == Set (q a)
compareTerm ?1 == a : ⊤
attempting shortcut ?1 := a
solving _13 := a

-}

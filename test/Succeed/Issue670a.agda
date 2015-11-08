{-# OPTIONS --show-implicit #-}
-- {-# OPTIONS -v tc.constr.findInScope:10 #-} -- -v tc.conv.elim:25 #-}
-- Andreas, 2012-07-01
module Issue670a where

import Common.Level
open import Common.Equality

findRefl : {A : Set}(a : A){{p : a ≡ a}} → a ≡ a
findRefl a {{p}} = p

uip : {A : Set}{a : A} → findRefl a ≡ refl
uip = refl
-- this should work.  Used to throw an internal error in Conversion,
-- because the solution for p was refl applied to parameters, instead of just refl.

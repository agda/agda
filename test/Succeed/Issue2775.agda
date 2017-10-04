-- Andreas, 2017-10-04, ignore irrelevant arguments during with-abstraction
-- Feature request by xekoukou

{-# OPTIONS --allow-unsolved-metas --show-irrelevant #-}

-- {-# OPTIONS -v tc.abstract:100 #-}

open import Agda.Builtin.Equality
open import Agda.Builtin.Bool

not : Bool → Bool
not true  = false
not false = true

but : Bool → .(Bool → Bool) → Bool
but true  f = false
but false f = true

test : (x : Bool) → but x not ≡ true
test x with but x not' where
  not' : Bool → Bool
  not' true  = false
  not' false = true
test x | true = refl
test x | false = _  -- unsolved meta ok

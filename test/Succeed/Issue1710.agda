-- Andreas, 2015-11-09, issue 1710 reported by vejkse
-- {-# OPTIONS -v tc.with:20 #-}

record wrap (A : Set) : Set where
  field
    out : A
open wrap public

record MapsFrom (A : Set) : Set₁ where
  field
    cod : Set
    map : A → cod
open MapsFrom public

wrapped : (A : Set) → MapsFrom A
cod (wrapped A) = wrap A
out (map (wrapped A) a) with a
... | _ = a

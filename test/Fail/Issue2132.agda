-- Andreas, 2016-08-08, issue #2132 reported by effectfully
-- Pattern synonyms in lhss of display form definitions

-- {-# OPTIONS -v scope:50 -v tc.decl:10 #-}

open import Common.Equality

data D : Set where
  C c : D
  g : D → D

pattern C′ = C

{-# DISPLAY C′ = C′ #-}
{-# DISPLAY g C′ = c #-}

-- Since pattern synonyms are now expanded on lhs of DISPLAY,
-- this behaves as
-- {-# DISPLAY C = C′ #-}
-- {-# DISPLAY g C = c #-}

test : C ≡ g C
test = refl

-- Expected error:
-- C′ != c of type D
-- when checking that the expression refl has type C′ ≡ c

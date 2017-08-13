-- Andreas, 2015-06-28, issue reported by Nisse

{-# OPTIONS -vtc.pos.occ:20 #-} -- KEEP!, this triggered the __IMPOSSIBLE__

-- {-# OPTIONS -v tc.pos.occ:70 -v tc.rec:80 --show-implicit #-}

-- {-# OPTIONS -v impossible:10 #-}
-- {-# OPTIONS -v reify.clause:60 #-}

data ⊥ : Set where

F : ⊥ → Set
F ()

record R (i : ⊥) : Set₁ where
  constructor c
  field
    P Q : F i → Set

-- An internal error has occurred. Please report this as a bug.
-- Location of the error: src/full/Agda/Syntax/Translation/InternalToAbstract.hs:874

-- The error is triggered by the use of prettyTCM in
-- Agda.TypeChecking.Positivity.getOccurrences.

-- tel = (_ : Prop) (_ : Prop) -- WRONG
-- perm = id
-- ps = (c x x : R @0) _
-- body = λ x _y _z -> x _z
-- type = F @1 → Set

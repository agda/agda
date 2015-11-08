{-# OPTIONS --allow-unsolved-metas #-}
-- {-# OPTIONS -v tc.meta:45 #-}

-- Andreas, 2014-12-07 found a bug in pruning

open import Common.Prelude
open import Common.Product
open import Common.Equality

postulate
  f : Bool → Bool

test : let
    X : Bool → Bool → Bool
    X = _
    Y : Bool
    Y = _
  in ∀ b → Y ≡ f (X b (f (if true then true else b))) ×
            (∀ a → X a (f b) ≡ f b)
test b = refl , λ a → refl

-- ERROR WAS:

-- Cannot instantiate the metavariable _22 to solution f b since it
-- contains the variable b which is not in scope of the metavariable
-- or irrelevant in the metavariable but relevant in the solution
-- when checking that the expression refl has type (_22 ≡ f b)

-- Here, Agda complains although there is a solution

--   X a b = b
--   Y = f (f true)

-- Looking at the first constraint

--   Y = f (X b (f (if true then true else b)))

-- agda prunes *both* arguments of X since they have rigid occurrences
-- of b.  However, the second occurrences goes away by normalization:

--   Y = f (X b (f true))

-- For efficiency reasons, see issue 415 , Agda first does not
-- normalize during occurs check.  Thus, the free variable check for
-- the arg (if true then true else b) returns b as rigid, which means
-- we have a neutral term (f (...b...)) with a rigid occurrence of bad
-- variable b, and we prune this argument of meta X.  This is unsound,
-- since the free variable check only returns a superset of the actual
-- (semantic) variable dependencies.

-- NOW: metas should be unsolved.

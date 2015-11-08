-- Andreas, 2015-09-18 Andreas, reported by Andrea
-- {-# OPTIONS -v impossible:10 #-}
-- {-# OPTIONS -v tc.cover.splittree:10 #-}
-- {-# OPTIONS -v tc.cc:30 #-}

open import Common.Bool
open import Common.Product
open import Common.Equality

postulate
 A : Set
 a : A

Works : A × A → Bool → A
Works (x , y) true = y
Works d false = a

works : ∀{x y} → Works (x , y) false ≡ a
works = refl

Test : A × (A × A) → Bool → A
Test (x , (y , z)) true = z
Test d false = a

test : ∀{x y z} → Test (x , (y , z)) false ≡ a
test = refl

-- ERROR WAS:
-- An internal error has occurred. Please report this as a bug.
-- Location of the error: src/full/Agda/TypeChecking/CompiledClause/Match.hs:189

-- Behavior of clause compiler WAS:
-- splitting on 0 after expandCatchAlls True:
--   (x,(y,z)) true -> z
--   (_,_)     false -> a
--   _         false -> a
-- splitting on 1 after expandCatchAlls False:
--   d false -> a
-- splitting on 1 after expandCatchAlls False:  <== NOW: True
--   x (y,z) true  -> z
--   _ (_,_) false -> a  <== WAS MISSING
--   _ _     false -> a
-- splitting on 2 after expandCatchAlls False:
--   _ _ false -> a
-- splitting on 3 after expandCatchAlls False:
--   x y z true  -> z
--   x y z false -> a  <== WAS MISSING

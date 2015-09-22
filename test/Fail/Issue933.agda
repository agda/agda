-- {-# OPTIONS -v tc.conv:10 #-}

-- 2013-11-03 Reported by sanzhiyan

module Issue933 where

record RGraph : Set₁ where
  field
    O : Set
    R : Set
    refl : O -> R

module Families (Γ : RGraph) where

 module Γ = RGraph Γ

 record RG-Fam : Set₁ where
  field
    O : Γ.O -> Set
    refl : ∀ {γo} -> (o : O γo) → O (Γ.refl γo)

-- "O (Γ.refl γo)" should be a type error.

-- Andreas: Fixed.  SyntacticEquality wrongly just skipped projections.

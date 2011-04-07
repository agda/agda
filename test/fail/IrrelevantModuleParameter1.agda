module IrrelevantModuleParameter1 (A : Set) .(a : A) where

postulate 
  P : A -> Set
  p : P a
-- cannot use a here, because it is irrelevant
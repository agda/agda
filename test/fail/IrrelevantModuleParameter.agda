module IrrelevantModuleParameter .(A : Set) where

postulate 
  a : A
-- cannot declare something of type A, since A is irrelevant
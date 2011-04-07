-- Andreas, 2011-04-07

module IrrelevantTelescope where

data Wrap .(A : Set) : Set where
  wrap : A -> Wrap A 
-- cannot use A, because it is declared irrelevant

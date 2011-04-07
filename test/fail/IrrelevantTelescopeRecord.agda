-- Andreas, 2011-04-07

module IrrelevantTelescopeRecord where

record Wrap .(A : Set) : Set where
  field
    out : A
-- cannot use A, because it is declared irrelevant

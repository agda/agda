-- {-# OPTIONS -v tc.polarity:10 -v tc.pos.args:10 #-}
module UnsolvableLevelConstraintsInDataDef where

open import Common.Equality

data D : Set1 where
  abs : ∀ E → D ≡ E → (E → D) → D

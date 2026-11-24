{-# OPTIONS --double-check -WnoRecordStageName #-}
module RecordStageNamesCached where

open import Agda.Builtin.Bool

record R : Set₁ where
  field A : Set
  private
    F : Bool → Set
    F true = A
    F false = A → A
  field value : (b : Bool) → F b

make : (A : Set) (value : (b : Bool) → R.1.F A b) → R
make = R.constructor

module Public = R.1 Bool

-- No public definition refers to this helper, and no stage alias exports it.
-- It must nevertheless survive serialization for local stage access.
record Unused : Set where
  private
    unused : Set
    unused = Bool
  field value : Bool

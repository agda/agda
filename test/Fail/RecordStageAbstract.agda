{-# OPTIONS -WnoRecordStageName #-}
module RecordStageAbstract where

open import Agda.Builtin.Bool
open import Agda.Builtin.Equality

record R : Set where
  abstract
    T : Set
    T = Bool
  field x : T

-- Naming a stage must not unfold an abstract helper.
bad : R.0.T ≡ Bool
bad = refl

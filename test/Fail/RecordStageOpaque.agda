{-# OPTIONS -WnoRecordStageName #-}
module RecordStageOpaque where

open import Agda.Builtin.Bool
open import Agda.Builtin.Equality

record R : Set where
  opaque
    T : Set
    T = Bool
  field x : T

-- Naming a stage must not unfold an opaque helper.
bad : R.0.T ≡ Bool
bad = refl

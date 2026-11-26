module RecordStageNameWarning where

record R (A : Set) : Set where
  B = A
  field x : B

c : {A : Set} → R.0.B A → R A
c = R.constructor

-- Warn once here; using the alias does not contain a stage selector.
module S (A : Set) = R.0 A
c' : {A : Set} → S.B A → R A
c' = R.constructor

open R.0

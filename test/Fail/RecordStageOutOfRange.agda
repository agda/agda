module RecordStageOutOfRange where

record R (A : Set) : Set where
  B = A
  field x : B

bad = R.1.B

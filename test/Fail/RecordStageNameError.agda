{-# OPTIONS -Werror #-}
module RecordStageNameError where

record R (A : Set) : Set where
  B = A
  field x : B

bad = R.0.B

module RecordStagePrivateHelper where

record R : Set₁ where
  private
    T = Set
  field x : T

-- Privacy is retained in the final record module.
bad = R.T

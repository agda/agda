module RecordStagePrivate where

module M where
  record R (A : Set) : Set where
    B = A
    field x : B

-- M is not a lexical parent here.
bad = M.R.0.B

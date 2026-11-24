module RecordStageCopyPrivate where

module M (A : Set) where
  record R : Set where
    B = A
    field x : B

  module N (r : R) = R r
  -- Copying a module does not export its private stages, even within M.
  bad = N.0.B

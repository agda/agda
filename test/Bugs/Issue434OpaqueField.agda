-- A field inside an opaque block is flattened during scope checking, but the
-- record stage builder does not see it. This currently crashes checkRecordStages.
module Issue434OpaqueField where

record R (A : Set) : Set where
  opaque
    field a : A

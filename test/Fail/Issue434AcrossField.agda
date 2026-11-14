module Issue434AcrossField where

-- The signature and definition of Carrier infer a mutual block across fields.
-- Unfolding Carrier would give the constructor arguments
-- (value : later) (later : Set): the first argument depends on a later one.
record R : Set₁ where
  Carrier : Set

  field
    value : Carrier
    later : Set

  Carrier = later

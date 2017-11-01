-- Andreas, 2017-11-01, issue #2831

-- The following pragma should trigger a warning, since the mutual block
-- does not contain anything the pragma could apply to.

{-# NO_POSITIVITY_CHECK #-}
mutual
  postulate
    A : Set

-- EXPECTED WARNING:
-- No positivity checking pragmas can only precede a data/record
-- definition or a mutual block (that contains a data/record
-- definition).

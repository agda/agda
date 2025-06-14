-- Andreas, 2025-06-14, issue #7944
-- The @0 of a local where modulo should not be applied
-- to the clause rhs!

{-# OPTIONS --erasure #-}

Test : @0 Set → Set
Test A = A
  module @0 _ where
    -- The contents of this where-module do not matter,
    -- as long as it is not empty.
    postulate _ : Set

-- Used to succeed (Agda 2.6.4, 2.7.0), should fail.

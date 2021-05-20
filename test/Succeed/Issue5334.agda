-- Andreas, 2021-04-21, issue #5334
-- Improve sorting of constructors to data for interleaved mutual blocks.

{-# OPTIONS --allow-unsolved-metas #-}

module Issue5334 where

module Works where

  data Nat : Set where
    zero : Nat
  data Fin : Nat → Set where
    zero : Fin {!!}

interleaved mutual

  data Nat : Set
  data Fin : Nat → Set
  data _ where
    zero : Nat
  data _ where
    zero : Fin {!!}  -- should work

-- Error was:
-- Could not find a matching data signature for constructor zero
-- There was no candidate.

module AbstractTermination where

data Nat : Set where
  zero : Nat
  suc : Nat → Nat

mutual

  f : Nat → Nat
  f n = g n
    where
      abstract
        g : Nat → Nat
        g n = f n

-- Andreas, 2016-10-03 re issue #2231.
-- Should give termination error.
-- Wrong behavior with Agda-2.3.2.
-- Correct behavior from at least Agda-2.4.2.2.

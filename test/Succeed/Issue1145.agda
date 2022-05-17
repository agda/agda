data ⊥ : Set where -- keep this on the first line!!

Type = Set  -- This should not be gobbled up under the data declaration

-- Andreas, 2021-04-15, issue #1145
-- Allow stacking of layout keywords on the same line.

-- This files contains tests for the new layout rules
-- and also tests from debugging the original implementation.
--
-- Some original failures where influenced by whether
-- there were comments or black lines, so please don't
-- "clean up" this file.

postulate A : Set; B : Set
          C : Set

-- First example

private postulate  -- Bar
  D : Set
  _>>_ : Set → Set → Set

module _ where
  private {- this block comment
             removes the line breaks
             between the layout keywords -} postulate
    D1 : Set
    E1 : Set

-- Second example

private module PM where              -- stack
  module PMM where
  private module PMPM1 where
          module PMPM2 where private -- stack
            module PMPM2M where
  module PMM2 where

-- Testing whether do-notation still works

test = do A; B
          C

let-example =
   let X = A
       in  B

do-example = do
  Set
  where
    Y : Set
    Y = A

F = Set

private
  doey = do
    Set
    where postulate poey : Set

E = Set

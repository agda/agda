-- {-# OPTIONS -v interaction.give:30 -v interaction.scope:30 -v highlighting:50 -v auto:10 #-}
-- Andreas, 2014-07-05 and -08

module _ where

data Unit : Set where
  unit : Unit

auto : Unit
auto = {!!}  -- C-c C-a succeeds but then an error occurs during highlighting

-- Problem WAS:
-- Auto finds a solution, but then there is the error
-- Failed to parse expression in ?0

-- Should work now.

refine : Unit
refine = {!unit!}

-- Problem WAS: Highlighting after refine triggers an error.


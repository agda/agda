-- Andreas, 2011-09-11
module Issue392 where
import Common.Irrelevance  

-- Create an non-irrelevant record R1 (at least one field relevant).
record R1 : Set1 where
  field
    .f1 : Set
    f1' : Set

{- This creates a module with an relevant record parameter

   module R1 (r : R1) where
     .f1 : Set -- = R1.f1 r
     f1' : Set    
-}

-- Create an irrelevant instance f2 of R1.
record R2 : Set2 where
  field
    .f2 : R1
    f3  : Set
  
-- This should not succeed.
  open R1 f2 public

{-
identifier f2 is declared irrelevant, so it cannot be used here
when checking that the expression f2 has type R1
-}
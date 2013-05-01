-- {-# OPTIONS -v interaction:50 #-}
module Issue841 where

postulate
  D : Set
  c : (A : Set) (B : Set1) → D
  e : (A : Set) (B : Set1) (C : Set2) (X : Set3) → D

-- When the following is refined the goals end up being the wrong way
-- around.
bad : D
bad = {!c ?!}

-- I.e. bad ?3 ?2 instead of bad ?2 ?3.

-- Andreas, 2013-05-01 should now be correct.

bad' : D
bad' = {!e ? ?!}

-- This works:
good : D
good = {!c!}

also-good : D
also-good = {!c ? ?!}

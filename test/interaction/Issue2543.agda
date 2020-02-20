-- Andreas, 2017-04-11, Issue 2543
-- Printing of second non-trivial with-pattern

-- {-# OPTIONS -v interaction.case:100 #-}

data D : Set where
  c : D → D

f : D → D
f y with c y
... | c z with c y
... | q = {!q!}  -- C-c C-c q

-- Was:
-- f y | c z | (c q) = ?

-- Expected:
-- f y | c z | c q = ?

-- Jesper, 2019-11-21, now:
-- ... | c q = ?

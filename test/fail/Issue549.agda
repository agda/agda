-- 2012-03-16 Andreas, fixing shift/reduce conflict introduced by record update
module Issue549 where

record M.R { A } : Set where
-- gives: Not a valid identifier M.R

-- If you remove the A, you get: Not a valid pattern
-- since then it is parsed as a record update expression

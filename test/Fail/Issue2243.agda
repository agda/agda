-- Andreas, 2016-10-08, issue #2243

-- {-# OPTIONS -v tc.cover.cover:100 #-}

open import Agda.Builtin.Char

f : Char → Char
f 'x' = 'x'
f 'x' = 'y'  -- should be marked as unreachable clause
f _ = 's'

-- Andreas, 2017-04-13, issue #2494, reported by identicalsnowflake
-- Consecutive hidden record fields confused the implicit argument insertion
-- due to lack of names in NamedArg.

-- {-# OPTIONS -v tc.lhs:30 #-}
-- {-# OPTIONS -v tc.term.args:100 #-}

postulate
  Red Blue : Set

record Colors : Set where
  field
    {red}  : Red
    {blue} : Blue

f : Colors → Red
f record { blue = blue } = blue

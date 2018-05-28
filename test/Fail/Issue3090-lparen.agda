-- Andreas, 2018-05-27, issue #3090, reported by anka-213
-- Parser should not raise internal error for invalid symbol in name

{-# BUILTIN NATURAL ( #-}

-- Should fail with a parse error, not internal error

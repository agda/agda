-- Andreas, 2021-09-06, issue #5545,
-- regression introduced by #5522 (fix for #5291).
--
-- Note: this test requires that there is no newline at the end of file.
-- So, it violates the whitespace requirement of fix-whitespace,
-- and needs to be an exception in the configuration of fix-whitespace.

{-# OPTIONS --allow-unsolved-metas #-}

-- No newline at end of file triggered "Unterminated {!" error.

_ : Set
_ = {! !}
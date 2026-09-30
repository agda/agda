-- Andreas, 2017-09-03, issue #2730:
-- Skip termination check when giving.

-- C-c C-SPC fails because of termination problems, but
-- C-u C-c C-SPC should succeed here.

f : Set
f = {! f !}

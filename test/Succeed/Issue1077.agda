-- Andreas, 2017-07-28, issue #1077

-- Agda's reconstruction of the top-level module can be confusing
-- in case the user puts some illegal declarations before the
-- top level module in error.

-- Thus, Agda now rejects the following if the anon. module is omitted.
-- If the user writes the anon. module, it should be accepted,
-- (even if it looks stupid in this case).

module _ where

foo = Set

module Issue1077 where

  bar = Set

-- Should be accepted.

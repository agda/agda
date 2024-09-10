-- Andreas, 2016-02-01, reported on 2014-12-08

module Issue1388 where

  indented = Set

not-indented = Set

-- Expected error:
-- No declarations allowed after top-level module.

-- Andreas, 2017-07-28, issue #1077
-- Agda's reconstruction of the top-level module can be confusing
-- in case the user puts some illegal declarations before the
-- top level module in error.

foo = Set

module Issue1077 where

  bar = Set

-- WAS: accepted, creating modules Issue1077 and Issue1077.Issue1077
-- with Issue1077.foo and Issue1077.Issue1077.bar

-- NOW: Error
-- Illegal declarations before top-level module

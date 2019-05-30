-- Andreas, 2019-05-29, issue #3818, reported by Matthew Daggitt

-- An external module name, i.e., the object of `import`,
-- should not be considered clashing with an internal module name.

module _ where

module Issue3818 where
  module M where         -- Internal module Issue3818.M.

open import Issue3818.M  -- Name unambiguous, since referring to file.

-- Should succeed instead of complaining about ambiguous Issue3818.M.

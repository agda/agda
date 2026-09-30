
module _ where

open import Common.Bool

private
  unused = true
  used = true

private
 module Private where
  not-in-scope = true

in-scope = used

-- History:
--
-- * Ulf, 2015-20-12 c823aa9a0e84816d3e36ea86e04e9f9caa536c4a
--   [ deadcode ] local private things are not in scope at top-level
--                but imported things should be
--   The previous restriction of the top level scope (7f47d51c) was a
--   bit draconian and removed not only local private definitions but
--   all imported things from the scope. This is fixed by this commit.
--
-- * Andreas, 2021-05-18, used as testcase for issue #4647

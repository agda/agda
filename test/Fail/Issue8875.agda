-- Andreas, 2026-10-24, issue #8875
-- Library 'lib' is depended upon in different versions:
--   lib-2.0 directly (via flag --library)
--   lib-1.0 via mid
-- This leads to an ambiguous module M.
-- We should warn about the library version conflict.

module Issue8875 where

import M

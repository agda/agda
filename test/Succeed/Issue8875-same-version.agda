-- Andreas, 2026-10-24, issue #8875
-- Warn about libraries depended on in different versions.
--
-- lib and lib-2.0 resolve to the same library, so no warning should be raised.

module Issue8875-same-version where

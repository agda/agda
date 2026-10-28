-- Andreas, 2026-10-24, issue #8875
-- Warn about libraries depended on in different versions.
--
-- lib-1.0 via mid, and lib (no version) which resolves to lib-2.0.

module Issue8875-unversioned where

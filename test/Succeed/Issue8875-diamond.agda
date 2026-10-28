-- Andreas, 2026-10-24, issue #8875
-- Warn about libraries depended on in different versions.
--
-- lib-1.0 via a and b (both via mid), and lib-2.0 directly.
-- The second occurrence of mid in the tree is not expanded.

module Issue8875-diamond where

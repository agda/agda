-- Andreas, 2018-03-23: issue #3007, reported by Fabian

-- An broken identifier followed by a comment and then the end of the file
-- caused an internal error during error reporting.
--
-- Should fail without internal error.

postulate _-- This is the end of the file!

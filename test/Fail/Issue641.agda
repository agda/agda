-- Andreas, 2013-10-30
-- Test whether verbosity options are honored before file is loaded.
-- See Issue641.flags

module Issue641 where

-- Provoke a scope checking error.

open NoSuchModule

-- Expected output is some debug messages about importing, plus the error,
-- like:

--   Getting interface for Issue641
--   Check for cycle
--   Issue641 is not up-to-date.
-- Creating interface for Issue641.
--   visited:
-- Issue641.agda:9,6-18
-- No such module NoSuchModule
-- when scope checking the declaration
--   open NoSuchModule

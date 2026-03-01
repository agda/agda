-- Andreas, 2026-03-01, issue #6173, report and test case by gallais

-- We import a hierarchical module without a module header
import Issue6173.Import

-- WAS: internal error

-- Expected  error: [ModuleNameUnexpected]
-- The name of the top level module does not match the file name. The module
-- Import (at Issue6173/Import.agda:1.1)
-- should probably be named Issue6173.Import
-- when scope checking the declaration
--   import Issue6173.Import

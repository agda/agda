-- Andreas, 2026-01-20, issue #8326 reported by Jesper
-- InfectiveImport for --two-level is raised when imported module has --cubical
-- because it is implied by --cubical.
-- However, we want to see only warnings for the original options.

import Agda.Builtin.Cubical.Glue

-- Expected error: [InfectiveImport]
-- Importing module Agda.Builtin.Cubical.Glue using the
-- --cubical[={full,erased,no-glue}] flag from a module which does
-- not.
-- when scope checking the declaration
--   import Agda.Builtin.Cubical.Glue

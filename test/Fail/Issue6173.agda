-- Andreas, 2022-10-10, issue #6137
-- Give good error when trying to import an unnamed module from a subdir.

import Issue6173.A

-- Expected error:

-- Add a top-level module name to file Issue6173/A.agda
-- because composite module names such as Issue6173.A
-- cannot be stably reconstructed automatically
-- when scope checking the declaration
--   import Issue6173.A

-- Andreas, 2024-03-29, issue #7208
-- Regression in 2.6.2: Internal error when importing an empty hierarchical module.

import Issue7208.A

-- Expected error:

-- Issue7208/A.agda can be accessed via several project roots.
-- Both A and Issue7208.A point to this file.
-- when scope checking the declaration

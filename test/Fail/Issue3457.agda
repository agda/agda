-- Andreas, 2019-02-24, issue #3457
-- Error messages for illegal as-clause

import Agda.Builtin.Nat Fresh-name as _

-- Previously, this complained about a duplicate module definition
-- with unspeakable name.

-- Expected error:
-- Not in scope: Fresh-name

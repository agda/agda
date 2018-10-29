-- Andreas, 2018-10-29, issue #3331

-- Document that using and renaming lists cannot overlap.

open import Agda.Builtin.Bool using (true) renaming (true to tt)

-- Expected error:
-- Repeated name in import directive: true

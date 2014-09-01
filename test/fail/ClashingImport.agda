-- Andreas, 2014-09-01 restored this test case

module ClashingImport where

postulate A : Set

import Imports.A
open Imports.A public

-- only a public import creates a clash
-- since an ambiguous identifier would be exported


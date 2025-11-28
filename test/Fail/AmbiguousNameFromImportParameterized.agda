-- Andreas, 2025-11-10, testcase for ambiguous name from import parametrized.

open import Common.Issue481ParametrizedModule
open import Common.Issue481ParametrizedModule Set

postulate
  bla : Bla

-- Error mentions internal name generated from
-- import Common.Issue481ParametrizedModule Set

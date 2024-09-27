-- Andreas, 2016-10-08 issue #2243
-- This is a test case reported at #708 by pepijnkokke

open import Common.Bool using (Bool; true; false)
open import Common.Reflection using (QName)

example : QName → Bool
example (quote Bool) = true
example (quote Bool) = false  -- unreachable clause
example _            = false

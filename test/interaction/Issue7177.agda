-- Andreas, 2024-03-10, issue #7177
-- Correct scope when introducing underscores
-- via pattern synonyms.

open import Agda.Builtin.Bool
open import Agda.Builtin.Equality

data D : Set where
  c : { i : true ≡ false } → D

pattern ff {i} = c {i}

works : D
works = c

-- yellow:
-- _i_6 : true ≡ false

test : D
test = ff

-- yellow:
-- _i_8
--   : Agda.Builtin.Bool.Bool.true Agda.Builtin.Equality.≡
--     Agda.Builtin.Bool.Bool.false

-- No scope for underscore.

-- Expected output:
--
-- _i_6 : true ≡ false  [ at ... ]
-- _i_8 : true ≡ false  [ at ... ]

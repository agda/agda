-- Andreas, 2024-07-19, PR #7379
-- Trigger error warning TooManyArgumentsToSort

{-# OPTIONS --omega-in-omega #-} -- To only trigger the TooManyArgumentsToSort error

open import Agda.Primitive renaming (Set to Type; Setω to Typeω)

postulate
  l : Level

T : Type (lsuc l) l
T = Type l l

U : Typeω (lsuc l)
U = Typeω l


-- Expected errors:
-- Too many arguments given to sort Type... (4x)

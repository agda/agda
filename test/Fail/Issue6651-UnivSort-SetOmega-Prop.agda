-- Andreas, 2023-05-19, issue #6651
-- In Agda without extensions, Setω does not have a predecessor sort.

{-# OPTIONS --omega-in-omega #-}
{-# OPTIONS --prop #-}

open import Agda.Primitive

BEGIN = Set₁
END   = Set

mutual-block : BEGIN

Ω : Setω
Ω = _ -- Ambiguous, can be Setω or Propω

id : (A : Ω) → A → A
id A x = x

mutual-block = END

-- Expected error:
-- Failed to solve the following constraints:
--   univSort _3 = Setω (blocked on _3)

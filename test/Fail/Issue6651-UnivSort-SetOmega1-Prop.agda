-- Andreas, 2023-05-19, issue #6651
-- Only in Agda without --prop, Setω₁ has exactly one predecessor sort.

{-# OPTIONS --prop #-}

open import Agda.Primitive

BEGIN = Set₁
END   = Set

mutual-block : BEGIN

Ω : Setω₁
Ω = _ -- Setω

id : (A : Ω) → A → A
id A x = x

mutual-block = END

-- Expected error:
--
-- Failed to solve the following constraints:
--   univSort _3 = Setω₁ (blocked on _3)

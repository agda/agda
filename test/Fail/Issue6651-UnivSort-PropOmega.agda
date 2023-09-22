-- Andreas, 2023-05-19, issue #6651
-- Propω does not have a predecessor sort, even with --omega-in-omega.

{-# OPTIONS --omega-in-omega #-}
{-# OPTIONS --prop #-}

open import Agda.Primitive

BEGIN = Set₁
END   = Set

mutual-block : BEGIN

Ω : Propω
Ω = _ -- No solution

id : (A : Ω) → A → A
id A x = x

mutual-block = END

-- Expect a hard error:
--
-- univSort _2 != Propω
-- when checking that the solution _2 of metavariable _0 has the expected type Setω

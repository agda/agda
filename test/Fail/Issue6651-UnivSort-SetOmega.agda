-- Andreas, 2023-05-19, issue #6651
-- In Agda without extensions, Setω does not have a predecessor sort.

open import Agda.Primitive

mutual-block : Set₁

Ω : Setω
Ω = _ -- No solution

id : (A : Ω) → A → A
id A x = x

mutual-block = Set

-- Expect a hard error:
--
-- univSort _2 != Setω
-- when checking that the solution _2 of metavariable _0 has the expected type Setω

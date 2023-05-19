-- Andreas, 2023-05-19, issue #6651
-- LevelUniv is not a successor sort

{-# OPTIONS --level-universe #-}

open import Agda.Primitive

BEGIN = Set₁
END   = Set

mutual-block : BEGIN

Ω : LevelUniv
Ω = _ -- No solution

id : (A : Ω) → A → A
id A x = x

mutual-block = END

-- Expect a hard error, rather than just unsolved constraints:
--
-- univSort _ != LevelUniv

-- Andreas, 2023-05-19, issue #6651
-- SizeUniv is not a successor sort

{-# OPTIONS --sized-types #-}

open import Agda.Primitive
open import Agda.Builtin.Size

BEGIN = Set₁
END   = Set

mutual-block : BEGIN

Ω : SizeUniv
Ω = _ -- No solution

id : (A : Ω) → A → A
id A x = x

mutual-block = END

-- Expect a hard error, rather than just unsolved constraints:
--
-- univSort _ != SizeUniv

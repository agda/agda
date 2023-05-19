-- Andreas, 2023-05-19, issue #6651
-- IUniv is not a successor sort

{-# OPTIONS --cubical #-}

open import Agda.Primitive
open import Agda.Primitive.Cubical

BEGIN = Set₁
END   = Set

mutual-block : BEGIN

Ω : IUniv
Ω = _ -- No solution

id : (A : Ω) → A → A
id A x = x

mutual-block = END

-- Expect a hard error, rather than just unsolved constraints:
--
-- univSort _ != IUniv

-- Andreas, 2023-05-19, issue #6651
-- LockUniv is not a successor sort

{-# OPTIONS --guarded #-}

open import Agda.Primitive

BEGIN = Set₁
END   = Set

primitive
  primLockUniv : _

mutual-block : BEGIN

Ω : primLockUniv
Ω = _ -- No solution

id : (A : Ω) → A → A
id A x = x

mutual-block = END

-- Expect a hard error, rather than just unsolved constraints:
--
-- univSort _ != primLockUniv

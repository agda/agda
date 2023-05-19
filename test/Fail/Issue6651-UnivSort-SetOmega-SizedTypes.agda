-- Andreas, 2023-05-19, issue #6651
-- Predecessors of Setω if --omega-in-omega and --sized-types

{-# OPTIONS --omega-in-omega #-}  -- or --type-in-type
{-# OPTIONS --sized-types #-}     -- SizeUniv : Setω destroys unicity of solution

open import Agda.Primitive

BEGIN = Set₁
END   = Set

mutual-block : BEGIN

Ω : Setω
Ω = {!!} -- should stay unsolved, since we have two solutions

test : (A : {!!}) → A → Ω
test A _ = A

mutual-block = END

-- Should error out with unsolved constraints (not with hard error)!

-- Expected error:
-- Failed to solve the following constraints:
--   univSort _4 = Setω (blocked on _4)

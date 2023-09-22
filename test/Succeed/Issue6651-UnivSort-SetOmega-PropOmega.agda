-- Andreas, 2023-05-19, issue #6651
-- Propω can be a predecessor of Setω if --omega-in-omega

{-# OPTIONS --omega-in-omega #-}  -- or --type-in-type
{-# OPTIONS --prop #-}            -- for Propω
{-# OPTIONS --sized-types #-}     -- SizeUniv : Setω should not make a difference

open import Agda.Primitive

BEGIN = Set₁
END   = Set

mutual-block : BEGIN

Ω : Setω
Ω = _ -- should solve to Propω later

test : (A : Propω) → A → Ω
test A _ = A

mutual-block = END

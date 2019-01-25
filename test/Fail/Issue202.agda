{-# OPTIONS --no-universe-polymorphism #-}

module Issue202 where

open import Agda.Primitive public using (Level)
open import Imports.Test

module Test2 {ℓ : Level} (F : Foo ℓ) where

-- Test2.agda:4,31-36
-- The metavariable _1 cannot depend on ℓ because it does not depend
-- on any variables
-- when checking that the expression Foo ℓ has type _1

-- The code is accepted if universe polymorphism is turned on in
-- Test2.agda.

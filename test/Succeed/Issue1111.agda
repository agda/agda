{-# OPTIONS --allow-unsolved-metas #-}

-- {-# OPTIONS -v tc.rewrite:25 -v tc.with:40 --show-implicit #-}
-- {-# OPTIONS -v tc:100 #-}

-- Andreas, 2014-05-17, reported by Fabien Renaud.
-- Error in reification of interaction metas
-- leading to strange error messages for rewrite.

module _ where

open import Common.Prelude
open import Common.Equality

postulate comm : ∀{n m} → n + m ≡ m + n

-- module With where

--   foo : ∀{x y} → x + (x + y) ≡ x + (y + x)
--   foo {x} {y} with x + y | comm {x} {y}
--   foo | ._ | refl = refl


test0 : ∀{x y} → x + (x + y) ≡ x + (y + x)
test0 rewrite comm {n = {!!}} {m = {!!}} = {!!}

test : ∀{x y} → x + (x + y) ≡ x + (y + x)
test {x}{y} rewrite comm {n = {!!}} {m = {!!}} = {!!}

-- Error WAS:
-- .Agda.Primitive.Level !=< Nat of type Set
-- when checking that the expression ?0 has type Nat

-- Now this type checks.

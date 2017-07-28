-- Andreas, 2017-07-28, issue #883
-- Was fixed by making rewrite not go through abstract syntax.

open import Agda.Builtin.Equality

test : (A : Set) → (a : A) → A
test A a rewrite refl {x = a} = a

-- WAS:
-- Setω !=< Level of type Setω
-- when checking that the type
-- (A : Set) (a w : A) →
-- _≡_ {_6 A w} {_A_9 A w} (_x_10 A w) (_x_10 A w) → A
-- of the generated with function is well-formed

-- Should succeed.


open import Agda.Builtin.Equality

test : (A : Set) (x y : A) → x ≡ y → Set
test A .y y refl with A
test A .y y refl | X = ?

-- Jesper, 2018-12-03, issue #2892:
-- Error message is:
--    Ill-typed pattern after with abstraction:  y
--    (perhaps you can replace it by `_`?)
--    when checking that the clause ;Issue2892.with-14 A X y = ? has type
--    (A w : Set) (x : w) → Set
-- Implementing the suggestion makes the code typecheck, so this
-- behaviour is at least not obviously wrong.

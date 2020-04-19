-- Andreas, 2020-04-19, issue #4560, raised by Andrea
-- Having both matching on constructor and copattern matching
-- for non-eta records leads to loss of subject reduction.

open import Agda.Builtin.Equality

postulate
  A : Set
  a : A

record R : Set where
  constructor con
  no-eta-equality
  field
    X Y : A

foo : R → A
foo (con x y) = x

-- Expected error here:
-- Pattern matching on no-eta record types is by default not allowed
-- when checking that the pattern con x y has type R

bar : R
bar .R.X = a
bar .R.Y = a

test : foo bar ≡ a
test = refl

-- Problem was:
-- foo bar != a of type A
-- when checking that the expression refl has type foo bar ≡ a

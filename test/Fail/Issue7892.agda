-- Andreas, 2025-11-17, issue #7892 is fixed.
-- Report and test case 2025-05-26 by Amy.
-- Updated to prove False by Szumi 2025-06-01.

open import Agda.Builtin.String
open import Agda.Builtin.Nat

data ⊥ : Set where

record R (x : String) : Set₁ where
  field
    foo : Set

module X {z : ⊥} (r : R "foo") where
  open R r using (foo) public
open X

test : R "bar" → Set

it : ⊥
it = _ -- yellow.  WAS: this meta is solved to "bar"

test r = foo {it} r

-- Expected error: [UnequalTerms]
-- "bar" !=< "foo" of type String
-- when checking that the expression r has type R "foo"

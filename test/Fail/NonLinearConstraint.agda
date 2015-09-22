module NonLinearConstraint where

import Common.Level
open import Common.Equality

test : let X : Set -> Set -> Set
           X = _
       in (A : Set) -> X A A ≡ A
test A = refl
-- should not be solved, solution not uniquely determined

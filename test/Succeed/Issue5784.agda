-- Andreas, 2022-03-02, issue #5784, reported by Trebor-Huang
-- Test case by Ulf Norell

-- primEraseEquality needs to normalized the sides of the equation,
-- not just reduce them.

open import Agda.Builtin.Nat
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Erase

data Wrap : Set where
  wrap : Nat → Wrap

test : wrap (1 + 1) ≡ wrap 2
test = primEraseEquality refl

thm : test ≡ refl
thm = refl

-- Should succeed
-- WAS: primEraseEquality refl != refl

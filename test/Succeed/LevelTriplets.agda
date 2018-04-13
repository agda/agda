
-- Check that we can solve level inequalities involving three variables.

module _ where

open import Agda.Primitive
open import Agda.Builtin.Equality

data Constraint : Set where
  mkConstraint : (a b : Level) → a ≡ b → Constraint

infix 0 _:=_
pattern _:=_ x y = mkConstraint x y refl

postulate l : Level

mutual-block : Set

a b c : Level
a = _
b = _
c = _

_ = a := a ⊔ b ⊔ c
_ = b := a ⊔ b ⊔ c
_ = c := a ⊔ b ⊔ c
_ = l := a ⊔ b ⊔ c   -- to actually solve it

mutual-block = Level

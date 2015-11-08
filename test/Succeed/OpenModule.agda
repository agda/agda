
module OpenModule where

module A where
  postulate X : Set

-- Both open import and open module applies the directives
-- to the "open" rather than to the module.
open import Nat   hiding (zero) renaming (Nat to N)
open module B = A renaming (X to Y)

Test : Set
Test = Y → B.X → N → Nat.Nat

zero : N
zero = Nat.zero

-- If the module isn't opened the directives are applied to
-- the module.
import Nat as N renaming (Nat to N)
module C = A    renaming (X to Z)

Test₂ : Set
Test₂ = N.N → C.Z

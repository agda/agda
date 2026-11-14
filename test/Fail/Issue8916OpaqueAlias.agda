module Issue8916OpaqueAlias where

open import Agda.Builtin.Equality
open import Agda.Builtin.Nat

record R : Set₁ where
  opaque
    Alias : Set
    Alias = Nat
  field value : Alias

-- Helper definitions in field types are expanded in the constructor
-- telescope, even when the field is outside the opaque block.
project : R → Nat
project = R.value

-- The helper itself must still be opaque.
test : (r : R) → R.Alias r ≡ Nat
test r = refl

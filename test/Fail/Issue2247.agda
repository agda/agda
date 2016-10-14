module _ where

open import Agda.Builtin.Equality

module MM1 (A : Set) where
  postulate a0 : A

  module M1 (a : A) where
    postulate
      x : A

  module M = M1 a0

module MM2 (A : Set) where

  open module MM1A = MM1 A

  check : M1.x ≡ (λ a → a)
  check = refl  -- used to be internal error


module Issue642 where

module M₁ (X : Set) where
  postulate F : X → Set

module M₂ (X : Set) where
  open M₁ X public

postulate
  A : Set
  x : A

open M₂ A

foo : F x
foo = {!!}

-- The goal was displayed as M₁.F A x rather than F x. If "open M₂ A"
-- is replaced by "open M₁ A", then the goal is displayed correctly.
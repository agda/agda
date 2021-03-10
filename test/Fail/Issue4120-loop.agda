{-# OPTIONS --prop --show-irrelevant #-}

open import Agda.Builtin.Equality

postulate
  A : Set
  P : Prop
  f : P → A
  g : A → P

{-# TERMINATING #-}
loop : A → A
loop y = loop y

mutual
  X : A
  X = _

  test : ∀ y → X ≡ f (g (loop y))
  test y = refl

-- The occurs check should not try to normalize the argument `loop y`
-- because it only appears in an irrelevant context.

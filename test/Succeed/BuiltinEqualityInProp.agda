-- Jesper, 2018-10-29 (comment on #3332): Besides for rewrite, builtin
-- equality is also used for primErase and primForceLemma. But I don't
-- see how it would hurt to have these use a Prop instead of a Set for
-- equality.

{-# OPTIONS --prop #-}

data _≡_ {A : Set} (a : A) : A → Prop where
  refl : a ≡ a
{-# BUILTIN EQUALITY _≡_ #-}

-- Andreas, 2023-10-20, issue #6639, testcase by Amy.
-- We can't have both of these:
-- * accept proofs as termination argument using the `c h > h args` structural ordering
-- * impredicative prop

{-# OPTIONS --prop #-}

data ⊥ : Prop where

-- * Either we have to reject impredicative propositions,
-- such as this impredicative encoding of truth.
-- True ≅ (P : Prop) → P → P
--
-- {-# NO_UNIVERSE_CHECK #-}
data True : Prop where
  c : ((P : Prop) → P → P) → True

true : True
true = c (λ P p → p)

-- * Or we have to reject the following recursion on proofs in the termination checker.
-- (Impredicativity is incompatible with the structural ordering `c h > h args`
-- without further restrictions.)
--
false : True → ⊥
false (c h) = false (h True true)

absurd : ⊥
absurd = false true

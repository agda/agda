-- Tests a non-productive coinductive function
{-# OPTIONS --prop --type-in-type --type-based-termination --no-syntax-based-termination #-}
module TypeBasedTermination.ImpredicativeProp where

data ⊥ : Prop where

data Bad : Prop where
  b : ((P : Prop) → P → P) → Bad

bad : Bad
bad = b (λ P p → p)

no-bad : Bad → ⊥
no-bad (b x) = no-bad (x Bad bad)

very-bad : ⊥
very-bad = no-bad bad

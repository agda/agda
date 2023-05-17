-- Andreas, Amy, 2023-05-17 return from AIM XXXVI
-- Add PTS rules (Prop, IUniv, SSet) and (IUniv, Prop, Prop)

{-# OPTIONS --two-level #-}
{-# OPTIONS --prop #-}

open Agda.Primitive
open import Agda.Primitive.Cubical

_ : (A : Prop) (B : IUniv) → _
_ = λ A B → A → B

-- WAS: funSort Prop IUniv is not a valid sort
-- Should solve to SSet

_ : (A : IUniv) (B : Prop) → _
_ = λ A B → A → B

-- WAS: funSort IUniv Prop is not a valid sort
-- Should solve to Prop

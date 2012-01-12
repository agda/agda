{-# OPTIONS --allow-unsolved-metas #-}
-- When instantiating metas, we can't ignore variables occurring in
-- irrelevant terms. If we do the irrelevant terms will become illformed
-- (and we get __IMPOSSIBLE__s)
-- For instance
--   _42 := DontCare (Just (Var 0 []))
-- is a bad thing to do. In the example below we hit the __IMPOSSIBLE__ in
-- the rename function in TypeChecking.MetaVars.assign.
module DontIgnoreIrrelevantVars where

import Common.Level
import Common.Irrelevance  


record Category : Set₁ where
  field
    .Arr : Set

postulate C : Category

_∙_ : ∀ {A : Set} {B : A → Set} {C : Set} →
      (∀ {x} → B x → C) → (g : ∀ x → B x) → A → C
f ∙ g = λ x → f (g x)

Exp : (I : Set) → Category
Exp I = record { Arr = I → Category.Arr C }
  
postulate
  Functor : Category → Set

postulate
  flattenP : ∀ D → Functor D → Functor D
  flattenHʳ : ∀ J → Functor (Exp J) → Functor (Exp J)

flattenH : ∀ I → Functor (Exp I) → Functor (Exp I)
flattenH I = flattenHʳ _ ∙ flattenP _

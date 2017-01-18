{-# OPTIONS --show-irrelevant #-}

-- {-# OPTIONS -v tc:20 #-}

open import Agda.Primitive
open import Issue2408.LevelDependentOnIrrelevant

-- Provoke error message mentioning (ℓ a)

provokeError : Set₁
provokeError = X
  where
  X = _
  F' : (a : A) → X
  F' = F

-- If #2408 is solved by replacing irrelevant vars in levels by Prop,
-- we get a horrible error like:
--
--   Set (.Agda.Primitive.lsuc (l .(Prop))) != Set₁
--   when checking that the expression X has type Set₁

-- Expected error:
-- Set (lsuc (l a)) != Set₁
-- when checking that the expression F has type A → X

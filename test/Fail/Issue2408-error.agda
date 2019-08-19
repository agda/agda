{-# OPTIONS --show-irrelevant #-}

-- {-# OPTIONS -v tc:20 #-}

open import Agda.Primitive
open import Issue2408.LevelDependentOnIrrelevant

-- Provoke error message mentioning (ℓ a)

provokeError : (a : A) → Set₁
provokeError a = Set (l a)

-- If #2408 is solved by replacing irrelevant vars in levels by Prop,
-- we get a horrible error like:
--
--   Set (.Agda.Primitive.lsuc (l .(Prop))) != Set₁
--   when checking that the expression Set (l a) has type Set₁

-- Expected error:
-- Set (lsuc (l a)) != Set₁
-- when checking that the expression Set (l a) has type Set₁

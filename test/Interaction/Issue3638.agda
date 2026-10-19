
-- Andreas, 2019-03-17, issue #3638
-- Making rewriting in interactive goals work in parametrized modules.

{-# OPTIONS --rewriting #-}

-- {-# OPTIONS -v rewriting:100 #-}
-- {-# OPTIONS -v tc.sig.param:60 #-}
-- {-# OPTIONS -v interactive.meta:10 #-}

open import Agda.Builtin.Equality
{-# BUILTIN REWRITE _≡_ #-}

module _ (A : Set) where

postulate
  a b c : A
  eq  : a ≡ b
  rew : c ≡ b

{-# REWRITE rew #-}

goal : a ≡ c
goal = {! eq !}  -- C-u C-u C-c C-.

-- Displays:
-- Goal: a ≡ c
-- Have: a ≡ b

-- Expected: Rewrite rule rew should be applied.
-- Goal: a ≡ b

-- Works now.

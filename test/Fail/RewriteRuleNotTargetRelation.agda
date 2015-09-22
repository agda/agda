{-# OPTIONS --rewriting #-}

-- 2014-05-27 Jesper and Andreas

postulate
  A : Set
  R : A → A → Set

{-# BUILTIN REWRITE R #-}
{-# REWRITE R #-}

-- Expected error:
-- R  does not target rewrite relation
-- when checking the pragma REWRITE R

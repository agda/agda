{-# OPTIONS --rewriting #-}

-- 2014-05-27 Jesper and Andreas

postulate
  A B : Set
  R   : A → B → Set

{-# BUILTIN REWRITE R #-}

-- Expected error:
-- R  does not have the right type for a rewriting relation
-- because the types of the last two arguments are different
-- when checking the pragma BUILTIN REWRITE R

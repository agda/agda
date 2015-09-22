{-# OPTIONS --rewriting #-}

-- 2014-05-27 Jesper and Andreas

postulate
  A : Set

{-# BUILTIN REWRITE A #-}

-- Expected error:
-- A  does not have the right type for a rewriting relation
-- because it should accept at least two arguments
-- when checking the pragma BUILTIN REWRITE A

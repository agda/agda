{-# OPTIONS --rewriting #-}

-- 2014-05-27 Jesper and Andreas

postulate
  A : Set
  a : A → A → A

{-# BUILTIN REWRITE a #-}

-- Expected error:

-- a  does not have the right type for a rewriting relation
-- because its type does not end in a sort, but in  A
-- when checking the pragma BUILTIN REWRITE a

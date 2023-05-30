-- Andreas, 2023-05-30, issue #6675
-- Need proper error for rewrite rules in data declarations.
-- Had been changed to internal error in #6615.

{-# OPTIONS --rewriting #-}

interleaved mutual

  data Id (A : Set) (a : A) : A → Set
  {-# BUILTIN REWRITE Id #-}

  data Id A a where
    refl : Id A a a
    {-# REWRITE refl #-}

-- Expected:

-- Illegal declaration in data type definition
--   {-# REWRITE refl #-}
-- when scope checking the declaration
--   data Id Aa where
--     refl : Id A a a
--     {-# REWRITE refl #-}

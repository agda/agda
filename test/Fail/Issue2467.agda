-- Andreas, 2017-02-20, issue #2467
-- Proper error on missing BUILTIN REWRITE

{-# OPTIONS --rewriting #-}

postulate A : Set

{-# REWRITE A #-}

-- Should fail with error like

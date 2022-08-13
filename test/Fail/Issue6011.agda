-- Andreas, 2022-08-13, issue #6011 reported by szumixie
--
-- Agda 2.6.3 dev version was crashing on a rewrite relation
-- that produced no name.  (Regression over 2.6.2.2.)

{-# OPTIONS --rewriting #-}

P : Set → Set → Set
P A B = A

{-# BUILTIN REWRITE P #-}

-- Should give proper error:
-- Invalid rewrite relation

{-# OPTIONS --experimental-irrelevance #-}

-- Andreas, 2015-05-18  Irrelevant module parameters
-- should not be resurrected in module body.

postulate
  A : Set

module M .(a : A) where

  bad : (..(_ : A) -> Set) -> Set
  bad f = f a
    -- SHOULD FAIL: variable a is declared irrelevant,
    -- so it cannot be used here.

-- This fails of course:
-- fail : .(a : A) -> (..(_ : A) -> Set) -> Set
-- fail a f = f a

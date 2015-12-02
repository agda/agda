-- Andreas, 2015-11-24, reported by Wolfram Kahl
{-# OPTIONS -v impossible:60 #-}
-- {-# OPTIONS -v tc.section:60 #-}
-- {-# OPTIONS -v scope:10 #-}
-- -- {-# OPTIONS -v tc.mod.apply:100 #-}

postulate N : Set

module A (O : Set) where

  record R : Set where
    field f : O

  module L where
    open R public

module B (P : Set) where

  module M (Q : Set) where
    -- private open module AQ = A Q public  -- Works, as module is named
    open A Q public  -- Did not work, as module is anonymous

  private open module MP = M P public
  -- OR: open MP public

open B
open L N

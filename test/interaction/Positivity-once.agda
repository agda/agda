-- The positivity checker should not be run twice for the same mutual
-- block. (If we decide to turn Agda into a total program, then we may
-- want to revise this decision.)

{-# OPTIONS -vtc.pos.graph:5 #-}

module Positivity-once where

A : Set₁

module M where

  B : Set₁
  B = A

A = Set

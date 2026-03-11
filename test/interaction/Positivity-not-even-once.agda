-- The positivity checker should not run if there's nothing that
-- needs occurrence and positivity computation.

{-# OPTIONS -vtc.pos.graph:5 #-}

module Positivity-not-even-once where

A : Set₁

module M where

  B : Set₁
  B = A

A = Set

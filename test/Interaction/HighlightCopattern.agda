{-# OPTIONS --copatterns #-}

module HighlightCopattern where

record WrapSet : Set₂ where
  field
    wrapped : Set₁
open WrapSet

my : WrapSet
wrapped my = Set    -- 'wrapped' should be highlighted in projection color

proj : WrapSet → Set₁
proj w = wrapped w  -- 'wrapped' should be highlighted in projection color

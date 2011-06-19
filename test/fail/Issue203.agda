{-# OPTIONS --universe-polymorphism #-}

module Issue203 where

open import Imports.Level

-- shouldn't work
data Bad {a b} (A : Set a) : Set b where
  [_] : (x : A) → Bad A

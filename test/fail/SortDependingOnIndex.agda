{-# OPTIONS --universe-polymorphism #-}
module SortDependingOnIndex where

open import Imports.Level

data Bad : (l : Level) → Set l where

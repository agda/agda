{-# OPTIONS --guardedness #-}

module CoInf where

open import Codata.Musical.Notation

-- Check that ∞ can be used as an "expression".
test : Set → Set
test = ∞

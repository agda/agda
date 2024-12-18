{-# OPTIONS --polarity #-}

module ExplicitPolarityVsPragma where

postulate f : (@++ A : Set) → Set

{-# POLARITY f - #-}

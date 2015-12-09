
postulate B : Set

module M where
  record ⊤ : Set where

module P (A : Set) where
  open M public

module PB = P B

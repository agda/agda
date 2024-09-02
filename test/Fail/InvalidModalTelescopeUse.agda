{-# OPTIONS --cohesion #-}

module _ where

postulate A : Set

module M (a : A) where
  b : A
  b = a

  @♭ c : A
  c = b

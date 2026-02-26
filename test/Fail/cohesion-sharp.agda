{-# OPTIONS --cohesion #-}
module _ where

data Sharp (@♯ A : Set) : Set where
  con : @♯ A → Sharp A


bad : {A : Set} -> Sharp A → A
bad (con a) = a

{-# OPTIONS --warning=error #-}
module Issue329b where

abstract
  infixl 0 D Undeclared
  data D : Set where

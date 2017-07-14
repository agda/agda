{-# OPTIONS --warning=error #-}
module Issue329c where

private
  infixl 0 D Undeclared
  data D : Set where

{-# OPTIONS --warning=error #-}
module Issue329 where

mutual
  infixl 0 D Undeclared
  data D : Set where

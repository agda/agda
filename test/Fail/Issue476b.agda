{-# OPTIONS --warning=error #-}

-- Useless abstract

module Issue476b where

abstract
  data A : Set

data A where

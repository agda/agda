{-# LANGUAGE GADTs #-}

module Issue223 where

data A where
  BA :: B -> A

data B where
  AB :: A -> B
  BB :: B


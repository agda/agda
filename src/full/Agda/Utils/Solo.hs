{-# LANGUAGE CPP #-}
module Agda.Utils.Solo
  ( Solo
  , pattern MkSolo
  )
  where

#if MIN_VERSION_base(4,18,0)

import Data.Tuple (Solo(MkSolo))

#else

import Data.Tuple (Solo(Solo))

pattern MkSolo :: a -> Solo a
pattern MkSolo a = Solo a

#endif

{-# LANGUAGE CPP #-} -- GHC 7.4.2 requires this indentation. See Issue 1460.
{-# LANGUAGE DoAndIfThenElse      #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE OverloadedStrings    #-}
{-# LANGUAGE TypeSynonymInstances #-}

module Main where

import qualified Exec.Tests as EXEC
import Test.Tasty
import Test.Tasty.Silver.Interactive as TM

#if __GLASGOW_HASKELL__ <= 708
import Control.Applicative ((<$>))
#endif

main :: IO ()
main = tests >>= TM.defaultMain

tests :: IO TestTree
tests = testGroup "all" <$> sequence [EXEC.tests]


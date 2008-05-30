{-# OPTIONS -cpp #-}

{-| A wrapper for readline. Makes it easier to handle absence of readline.
-}
module Agda.Utils.ReadLine where

#ifndef mingw32_HOST_OS
import qualified System.Console.Readline as RL
#endif
import System.IO

import Agda.Utils.Unicode
import Agda.Utils.Monad

readline   :: String -> IO (Maybe String)
addHistory :: String -> IO ()
#ifdef mingw32_HOST_OS
readline s = do
  putStr s
  hFlush stdout
  l <- getLine
  return $ Just $ fromUTF8 l
addHistory s = return ()
#else
readline   s = fmap fromUTF8 <$> RL.readline s
addHistory s = RL.addHistory $ toUTF8 s
#endif

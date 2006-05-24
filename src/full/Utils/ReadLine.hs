{-# OPTIONS -cpp #-}

{-| A wrapper for readline. Makes it easier to handle the absence of readline
    (not handled at the moment, though).
-}
module Utils.ReadLine where

import qualified System.Console.Readline as RL

import Utils.Unicode
import Utils.Monad

readline   :: String -> IO (Maybe String)
addHistory :: String -> IO ()
#ifdef mingw32_HOST_OS
readline   s = putStr s >> Just <$> getLine
addHistory s = return ()
#else
readline   s = fmap fromUTF8 <$> RL.readline s
addHistory s = RL.addHistory $ toUTF8 s
#endif

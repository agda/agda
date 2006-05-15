{-# OPTIONS -cpp #-}

{-| A wrapper for readline. Makes it easier to handle the absence of readline
    (not handled at the moment, though).
-}
module Utils.ReadLine where

import qualified System.Console.Readline as RL

import Utils.Unicode
import Utils.Monad

readline s  = fmap fromUTF8 <$> RL.readline s
addHistory  = RL.addHistory . toUTF8


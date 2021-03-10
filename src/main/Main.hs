-- | Wrapper for "Agda.Main".
--
-- Agda is installed as a library. This module is used to build the
-- executable.

module Main (main) where

import Agda.Main ( runAgda )
import Prelude ( IO )

main :: IO ()
main = runAgda []

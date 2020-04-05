-- | Wrapper for "Agda.Main".
--
-- Agda is installed as a library. This module is used to build the
-- executable.

module Main (main) where

import qualified Agda.Main ( runAgda )
import Agda.Compiler.Builtin ( builtinBackends )
import Prelude ( IO )

main :: IO ()
main = Agda.Main.runAgda builtinBackends

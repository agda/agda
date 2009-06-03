-- | Wrapper for "Agda.Main".
--
-- Agda is installed as a library. This module is used to build the
-- executable.

module Main (main) where

import qualified Agda.Main
import qualified Prelude ()

main = Agda.Main.main

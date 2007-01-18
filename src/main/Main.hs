-- | Wrapper for "AgdaMain".
--
-- Agda is installed as a library. This module is used to build the
-- executable.

module Main (main) where

import qualified AgdaMain

main = AgdaMain.main

module Agda.Compiler.Malfunction.Main (main) where

import Agda.Main (runAgda)

import qualified Agda.Compiler.Malfunction as Malfunction

-- | Invokes the agda-compiler with the additional malfunction backend.
main :: IO ()
main = runAgda [Malfunction.backend]

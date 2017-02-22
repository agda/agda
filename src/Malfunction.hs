module Malfunction (main) where

import qualified Backend as Malfunction
import Agda.Main (runAgda)

-- | Invokes the agda-compiler with the additional malfunction backend.
main :: IO ()
main = runAgda [Malfunction.backend]

module Test (main) where

import Backend
import Agda.Compiler.Backend

main = runAgda [backend]

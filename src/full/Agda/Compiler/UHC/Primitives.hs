module Agda.Compiler.UHC.Primitives
  ( primFunctions )
where

import Agda.Compiler.UHC.Interface
import Data.Map as M

-- | Primitives defined for the UHC backend. Maps primitive names to the AName of the function to call.
primFunctions :: Map String AName
primFunctions = M.fromList
    [(n, ANmCore $ "UHC.Agda.Builtins." ++ n) | n <-
        [
        -- String
          "primStringAppend"
        , "primStringEquality"
        -- Char
        , "primCharToNat"
        , "primCharEquality"
        ]
    ]

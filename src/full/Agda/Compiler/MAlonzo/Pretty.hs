------------------------------------------------------------------------
-- Pretty-printing of Haskell modules
------------------------------------------------------------------------

module Agda.Compiler.MAlonzo.Pretty where

import Data.Generics
import qualified Language.Haskell.Pretty as Pretty
import Language.Haskell.Syntax

import Agda.Compiler.MAlonzo.Encode

-- | Inserts disambiguating parentheses and encodes module names just
-- before pretty-printing.

prettyPrint :: (Pretty.Pretty a, Data a) => a -> String
prettyPrint = Pretty.prettyPrint .
              everywhere (mkT HsParen) .
              everywhere (mkT encodeModuleName)

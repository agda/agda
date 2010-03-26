
module Pretty where

import Text.PrettyPrint

class Pretty a where
  pretty     :: a -> Doc
  prettyPrec :: Int -> a -> Doc
  pretty = prettyPrec 0
  prettyPrec _ = pretty

paren :: Bool -> Doc -> Doc
paren True  = parens
paren False = id

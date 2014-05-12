module Text.PrettyPrint.Extended
    ( module Text.PrettyPrint
    , Pretty(..)
    , defaultShow
    , condParens
    ) where

import Text.PrettyPrint

class Pretty a where
  pretty     :: a -> Doc
  prettyPrec :: Int -> a -> Doc

  pretty = prettyPrec 0
  prettyPrec _ = pretty

defaultShow :: Pretty a => Int -> a -> ShowS
defaultShow p x = shows (prettyPrec p x)

condParens :: Bool -> Doc -> Doc
condParens True  = parens
condParens False = id

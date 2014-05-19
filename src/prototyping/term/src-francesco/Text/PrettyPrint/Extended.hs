module Text.PrettyPrint.Extended
    ( module Text.PrettyPrint
    , Pretty(..)
    , defaultShow
    , condParens
    , prettyApp
    ) where

import Text.PrettyPrint

import Syntax.Abstract (Name)

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

prettyApp :: Pretty a => Int -> Doc -> [a] -> Doc
prettyApp _p h [] = h
prettyApp  p h xs =
  condParens (p > 3) $ h <+> fsep (map (prettyPrec 4) xs )

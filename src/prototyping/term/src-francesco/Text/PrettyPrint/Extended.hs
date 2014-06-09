module Text.PrettyPrint.Extended
    ( module Text.PrettyPrint
    , Pretty(..)
    , render
    , defaultShow
    , condParens
    , prettyApp
    ) where

import Text.PrettyPrint hiding (render)
import qualified Text.PrettyPrint as PP

class Pretty a where
  {-# MINIMAL pretty | prettyPrec #-}

  pretty     :: a -> Doc
  prettyPrec :: Int -> a -> Doc

  pretty = prettyPrec 0
  prettyPrec _ = pretty

instance Pretty Int where
  pretty = PP.text . show

defaultShow :: Pretty a => Int -> a -> ShowS
defaultShow p x = shows (prettyPrec p x)

condParens :: Bool -> Doc -> Doc
condParens True  = parens
condParens False = id

prettyApp :: Pretty a => Int -> Doc -> [a] -> Doc
prettyApp _p h [] = h
prettyApp  p h xs =
  condParens (p > 3) $ h <+> fsep (map (prettyPrec 4) xs )

render :: Pretty a => a -> String
render = PP.render . pretty

instance Pretty a => Pretty [a] where
  pretty []       = text "[]"
  pretty (x : xs) = text "[" <> pretty x <> go xs
    where
      go []       = text "]"
      go (y : ys) = text "," <+> pretty y <> go ys

instance Pretty Doc where
  pretty = id

{-| Pretty printing functions.
-}
module Agda.Utils.Pretty
    ( module Agda.Utils.Pretty
    , module Text.PrettyPrint
    ) where

import Text.PrettyPrint

class Pretty a where
    pretty	:: a -> Doc
    prettyPrec	:: Int -> a -> Doc

    pretty	= prettyPrec 0
    prettyPrec	= const pretty

instance Pretty Doc where
    pretty = id

pwords :: String -> [Doc]
pwords = map text . words

fwords :: String -> Doc
fwords = fsep . pwords

mparens :: Bool -> Doc -> Doc
mparens True  = parens
mparens False = id



module Pretty where

import Text.PrettyPrint
import Syntax

class Pretty a where
    pretty :: a -> Doc
    prettyPrec :: Int -> a -> Doc

    pretty = prettyPrec 0
    prettyPrec _ = pretty

instance Pretty Ident where
    pretty (Ident x) = text x


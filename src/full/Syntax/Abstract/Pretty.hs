{-# OPTIONS -fglasgow-exts -fallow-undecidable-instances -fallow-overlapping-instances #-}
module Syntax.Abstract.Pretty where

import Syntax.Abstract
import Syntax.Concrete.Pretty ()
import Syntax.Translation.AbstractToConcrete
import Utils.Pretty

showA :: (Show c, ToConcrete a c) => a -> String
showA = show . abstractToConcrete_

prettyA :: (Pretty c, ToConcrete a c) => a -> Doc
prettyA = pretty . abstractToConcrete_

instance Show Expr where
    show = showA


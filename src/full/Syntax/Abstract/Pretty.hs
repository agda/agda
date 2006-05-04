{-# OPTIONS -fglasgow-exts #-}
module Syntax.Abstract.Pretty where

import Syntax.Abstract
import Syntax.Concrete.Pretty ()
import Syntax.Translation.AbstractToConcrete

showA :: (Show c, ToConcrete a c) => a -> String
showA = show . abstractToConcrete_

instance Show Expr where
    show = showA


{-# OPTIONS -fglasgow-exts -fallow-undecidable-instances -fallow-overlapping-instances #-}
module Syntax.Abstract.Pretty where

import Control.Applicative

import Syntax.Abstract
import Syntax.Concrete.Pretty ()
import Syntax.Translation.AbstractToConcrete
import TypeChecking.Monad
import Utils.Pretty

showA :: (Show c, ToConcrete a c, MonadTCM tcm) => a -> tcm String
showA x = show <$> abstractToConcrete_ x

prettyA :: (Pretty c, ToConcrete a c, MonadTCM tcm) => a -> tcm Doc
prettyA x = pretty <$> abstractToConcrete_ x

